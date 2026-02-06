----------------------- MODULE ECSSimG -----------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, CSV, IOUtils

CONSTANTS
    ShortTickets,       \* Capacity of short pool
    LongTickets,        \* Capacity of long pool
    ShortWaitLimit,     \* Queue limit for short tasks
    LongWaitLimit,      \* Queue limit for long tasks
    MaxSteps,           \* Simulation horizon
    ArrivalRate,        \* 0..100 (Probability of arrival per opportunity)
    CSVFile             \* Output filename

VARIABLES
    requestState,       \* Function: ActiveReqID -> State Enum
    ticketPool,         \* Function: {Short, Long} -> Integer
    waitSets,           \* Function: {Short, Long} -> Set of ReqIDs
    duration,           \* Function: ActiveReqID -> Integer
    step,               \* Current simulation step
    nextReqId,          \* Counter for generating unique IDs
    cumulativeDrops,    \* Counter: [Short->Int, Long->Int]
    
    \* NEW METRICS
    totalArrivals,      \* Total requests that attempted to enter (accepted + dropped on entry)
    totalCompleted      \* Total requests that successfully finished (Goodput)

Vars == <<requestState, ticketPool, waitSets, duration, step, nextReqId, cumulativeDrops, totalArrivals, totalCompleted>>

States == {"WaitingShort", "RunningShort", "WaitingLong", "RunningLong"}
TicketTypes == {"Short", "Long"}

-----------------------------------------------------------------------------

\* Type Invariant
TypeOK ==
    /\ requestState \in [DOMAIN requestState -> States]
    /\ ticketPool \in [TicketTypes -> Nat]
    /\ waitSets \in [TicketTypes -> SUBSET (DOMAIN requestState)]
    /\ \A t \in TicketTypes : ticketPool[t] <= (IF t="Short" THEN ShortTickets ELSE LongTickets)
    /\ duration \in [DOMAIN duration -> Nat]
    /\ totalArrivals \in Nat
    /\ totalCompleted \in Nat

-----------------------------------------------------------------------------

\* INITIALIZATION
Init ==
    /\ requestState    = <<>> 
    /\ ticketPool      = [Short |-> ShortTickets, Long |-> LongTickets]
    /\ waitSets        = [Short |-> {}, Long |-> {}]
    /\ duration        = <<>> 
    /\ step            = 0
    /\ nextReqId       = 1
    /\ cumulativeDrops = [Short |-> 0, Long |-> 0]
    /\ totalArrivals   = 0
    /\ totalCompleted  = 0

-----------------------------------------------------------------------------

\* HELPER: Remove Request from State (Garbage Collection)
RemoveRequest(r, currReqState, currDuration) ==
    [state |-> [x \in (DOMAIN currReqState) \ {r} |-> currReqState[x]],
     dur   |-> [x \in (DOMAIN currDuration) \ {r} |-> currDuration[x]]]

\* HELPER: Attempt Acquire with Shedding
AttemptAcquire(r, type, currPool, currWait, currReqState) ==
    IF currPool[type] > 0 THEN
        [pool     |-> [currPool EXCEPT ![type] = @ - 1],
         wait     |-> currWait,
         reqState |-> [currReqState EXCEPT ![r] = IF type="Short" THEN "RunningShort" ELSE "RunningLong"],
         dropped  |-> FALSE]
    ELSE IF Cardinality(currWait[type]) < (IF type="Short" THEN ShortWaitLimit ELSE LongWaitLimit) THEN
        [pool     |-> currPool,
         wait     |-> [currWait EXCEPT ![type] = @ \cup {r}],
         reqState |-> [currReqState EXCEPT ![r] = IF type="Short" THEN "WaitingShort" ELSE "WaitingLong"],
         dropped  |-> FALSE]
    ELSE
        [pool     |-> currPool,
         wait     |-> currWait,
         reqState |-> currReqState,
         dropped  |-> TRUE]

\* HELPER: Release Ticket
ReleaseTicket(type, currPool, currWait, currReqState) ==
    IF currWait[type] /= {} THEN
        LET waiter == CHOOSE w \in currWait[type] : TRUE IN
        [pool     |-> currPool,
         wait     |-> [currWait EXCEPT ![type] = @ \ {waiter}],
         reqState |-> [currReqState EXCEPT ![waiter] = IF type="Short" THEN "RunningShort" ELSE "RunningLong"]]
    ELSE
        [pool     |-> [currPool EXCEPT ![type] = @ + 1],
         wait     |-> currWait,
         reqState |-> currReqState]

\* HELPER: Simulation Stats & Tick
\* Updated to track Arrivals and Completions
RecordStats(newDrops, isArrival, isComplete) ==
    /\ step' = step + 1
    /\ cumulativeDrops' = [Short |-> cumulativeDrops.Short + (IF newDrops.Short THEN 1 ELSE 0),
                           Long  |-> cumulativeDrops.Long  + (IF newDrops.Long THEN 1 ELSE 0)]
    /\ totalArrivals'  = totalArrivals + (IF isArrival THEN 1 ELSE 0)
    /\ totalCompleted' = totalCompleted + (IF isComplete THEN 1 ELSE 0)

-----------------------------------------------------------------------------

\* ACTION 1: Spawn Request
SpawnRequest ==
    /\ step < MaxSteps
    /\ IF RandomElement(1..100) <= ArrivalRate THEN
           \* CASE A: A Request Arrives
           LET r == nextReqId
               newReqState == [x \in (DOMAIN requestState) \cup {r} |-> 
                               IF x=r THEN "Idle" ELSE requestState[x]]
               newDuration == [x \in (DOMAIN duration) \cup {r} |-> 
                               IF x=r THEN 
                                \* 90% chance to be Short (1-10ms), 10% chance to be Long (11-100ms)
                                    IF RandomElement(1..100) <= 90 
                                    THEN RandomElement(1..10) 
                                    ELSE RandomElement(11..100)
                               ELSE duration[x]]                                
           IN
           \* Try to acquire Short ticket
           LET outcome == AttemptAcquire(r, "Short", ticketPool, waitSets, newReqState) IN
               IF outcome.dropped THEN
                   \* Dropped on entry: Log it, but don't commit state changes
                   /\ ticketPool'   = outcome.pool
                   /\ waitSets'     = outcome.wait
                   /\ requestState' = requestState 
                   /\ duration'     = duration
                   /\ nextReqId'    = nextReqId + 1
                   \* Log: dropped=TRUE, isArrival=TRUE, isComplete=FALSE
                   /\ RecordStats([Short |-> TRUE, Long |-> FALSE], TRUE, FALSE)
               ELSE
                   \* Accepted: Commit new state
                   /\ ticketPool'   = outcome.pool
                   /\ waitSets'     = outcome.wait
                   /\ requestState' = outcome.reqState
                   /\ duration'     = newDuration
                   /\ nextReqId'    = nextReqId + 1
                   \* Log: dropped=FALSE, isArrival=TRUE, isComplete=FALSE
                   /\ RecordStats([Short |-> FALSE, Long |-> FALSE], TRUE, FALSE)
       ELSE
           \* CASE B: No Arrival (The "Clock Tick")
           /\ UNCHANGED <<ticketPool, waitSets, requestState, duration, nextReqId>>
           \* Log: dropped=FALSE, isArrival=FALSE, isComplete=FALSE
           /\ RecordStats([Short |-> FALSE, Long |-> FALSE], FALSE, FALSE)

\* ACTION 2: Complete (Garbage Collection)
Complete(r) ==
    /\ step < MaxSteps
    /\ requestState[r] \in {"RunningShort", "RunningLong"}
    /\ duration[r] <= 10
    /\ LET type == IF requestState[r] = "RunningShort" THEN "Short" ELSE "Long"
           outcome == ReleaseTicket(type, ticketPool, waitSets, requestState)
           clean   == RemoveRequest(r, outcome.reqState, duration) 
       IN
       /\ ticketPool'   = outcome.pool
       /\ waitSets'     = outcome.wait
       /\ requestState' = clean.state
       /\ duration'     = clean.dur
       /\ nextReqId'    = nextReqId
       \* Log: dropped=FALSE, isArrival=FALSE, isComplete=TRUE (Increment Goodput)
       /\ RecordStats([Short |-> FALSE, Long |-> FALSE], FALSE, TRUE)

\* ACTION 3: Short Yield
ShortYieldToLong(r) ==
    /\ step < MaxSteps
    /\ requestState[r] = "RunningShort"
    /\ duration[r] > 10
    /\ LET relRes == ReleaseTicket("Short", ticketPool, waitSets, requestState)
           acqRes == AttemptAcquire(r, "Long", relRes.pool, relRes.wait, relRes.reqState) 
       IN
       IF acqRes.dropped THEN
            \* Dropped during transition
            LET clean == RemoveRequest(r, acqRes.reqState, duration) IN
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = clean.state
            /\ duration'     = clean.dur
            /\ nextReqId'    = nextReqId
            \* Log: dropped=TRUE (Long), isArrival=FALSE, isComplete=FALSE
            /\ RecordStats([Short |-> FALSE, Long |-> TRUE], FALSE, FALSE)
       ELSE
            \* Successful transition
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = acqRes.reqState
            /\ duration'     = [duration EXCEPT ![r] = @ - 10]
            /\ nextReqId'    = nextReqId
            \* Log: dropped=FALSE, isArrival=FALSE, isComplete=FALSE
            /\ RecordStats([Short |-> FALSE, Long |-> FALSE], FALSE, FALSE)

\* ACTION 4: Long Yield Loop
LongYieldLoop(r) ==
    /\ step < MaxSteps
    /\ requestState[r] = "RunningLong"
    /\ duration[r] > 10
    /\ LET relRes == ReleaseTicket("Long", ticketPool, waitSets, requestState)
           acqRes == AttemptAcquire(r, "Long", relRes.pool, relRes.wait, relRes.reqState) 
       IN
       IF acqRes.dropped THEN
            \* Dropped during loop
            LET clean == RemoveRequest(r, acqRes.reqState, duration) IN
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = clean.state
            /\ duration'     = clean.dur
            /\ nextReqId'    = nextReqId
            /\ RecordStats([Short |-> FALSE, Long |-> TRUE], FALSE, FALSE)
       ELSE
            \* Successful re-entry
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = acqRes.reqState
            /\ duration'     = [duration EXCEPT ![r] = @ - 10]
            /\ nextReqId'    = nextReqId
            /\ RecordStats([Short |-> FALSE, Long |-> FALSE], FALSE, FALSE)

-----------------------------------------------------------------------------

\* Next State Logic
Next ==
    \/ SpawnRequest
    \/ \E r \in DOMAIN requestState : Complete(r)
    \/ \E r \in DOMAIN requestState : ShortYieldToLong(r)
    \/ \E r \in DOMAIN requestState : LongYieldLoop(r)


\* Constraint to Write CSV at end
AtTermination ==
    IF step = MaxSteps THEN
        /\ IF CSVRecords(CSVFile) = 0 THEN 
               CSVWrite("%s", << "step,arrivals,completed,shortDrops,longDrops" >>, CSVFile) 
           ELSE TRUE
        /\ CSVWrite("%s,%s,%s,%s,%s", 
                    << step, totalArrivals, totalCompleted, 
                       cumulativeDrops.Short, cumulativeDrops.Long >>, CSVFile)
        /\ IOExec(<<"/usr/bin/env", "Rscript", "vis_drops.R", CSVFile>>).exitValue = 0
        /\ FALSE
    ELSE TRUE

Spec == Init /\ [][Next]_Vars

=============================================================================
rm *.csv ; tlc ECSSim -note -generate -depth -1

-depth -1 for going until execution done 
-depth 100 for going for 100 steps

