----------------------- MODULE ECSsim -----------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, CSV, IOUtils

CONSTANTS
    ShortTickets,       \* Capacity of short pool
    LongTickets,        \* Capacity of long pool
    ShortWaitLimit,     \* Queue limit for short tasks
    LongWaitLimit,      \* Queue limit for long tasks
    MaxSteps,           \* Simulation horizon
    ArrivalRate,        \* 0..100 (Probability of arrival per opportunity)
    IOPercentage,       \* 0..100 (Probability a running task is IO-blocked) 
    SampleInterval,     \* Integer > 0: sampling interval in steps
    CSVFile             \* Output filename

VARIABLES
    requestState,       \* Function: ActiveReqID -> State Enum
    ticketPool,         \* Function: {Short, Long} -> Integer
    waitSets,           \* Function: {Short, Long} -> Set of ReqIDs
    duration,           \* Function: ActiveReqID -> Integer
    step,               \* Current simulation step
    nextReqId,          \* Counter for generating unique IDs
    cumulativeDrops,    \* Counter: [Short->Int, Long->Int]
    sampleCount,        \* Number of samples recorded
    totalShortWasteNum, \* Sum: IOPercentage^shortRun over samples
    totalShortWasteDen, \* Sum: 100^shortRun over samples
    totalLongWasteNum,  \* Sum: IOPercentage^longRun over samples
    totalLongWasteDen,  \* Sum: 100^longRun over samples
    totalShortWasteScaled, \* Scaled sum for short waste
    totalLongWasteScaled   \* Scaled sum for long waste

Vars == <<requestState, ticketPool, waitSets, duration, step, nextReqId, cumulativeDrops, sampleCount, totalShortWasteNum, totalShortWasteDen, totalLongWasteNum, totalLongWasteDen, totalShortWasteScaled, totalLongWasteScaled>>

States == {"WaitingShort", "RunningShort", "WaitingLong", "RunningLong"}
TicketTypes == {"Short", "Long"}

-----------------------------------------------------------------------------

\* Type Invariant: Ensures tickets are conserved and state is valid
TypeOK ==
    /\ requestState \in [DOMAIN requestState -> States]
    /\ ticketPool \in [TicketTypes -> Nat]
    /\ waitSets \in [TicketTypes -> SUBSET (DOMAIN requestState)]
    /\ \A t \in TicketTypes : ticketPool[t] <= (IF t="Short" THEN ShortTickets ELSE LongTickets)
    /\ duration \in [DOMAIN duration -> Nat]
    /\ sampleCount \in Nat
    /\ totalShortWasteNum \in Nat
    /\ totalShortWasteDen \in Nat
    /\ totalLongWasteNum \in Nat
    /\ totalLongWasteDen \in Nat
    /\ totalShortWasteScaled \in Nat
    /\ totalLongWasteScaled \in Nat

-----------------------------------------------------------------------------

\* INITIALIZATION
Init ==
    /\ requestState    = <<>>  \* Empty function (No active requests)
    /\ ticketPool      = [Short |-> ShortTickets, Long |-> LongTickets]
    /\ waitSets        = [Short |-> {}, Long |-> {}]
    /\ duration        = <<>>  \* Empty function
    /\ step            = 0
    /\ nextReqId       = 1     \* Start IDs at 1
    /\ cumulativeDrops = [Short |-> 0, Long |-> 0]
    /\ sampleCount = 0
    /\ totalShortWasteNum = 0
    /\ totalShortWasteDen = 0
    /\ totalLongWasteNum = 0
    /\ totalLongWasteDen = 0
    /\ totalShortWasteScaled = 0
    /\ totalLongWasteScaled = 0

-----------------------------------------------------------------------------

\* HELPER: Remove Request from State (Garbage Collection)
RemoveRequest(r, currReqState, currDuration) ==
    [state |-> [x \in (DOMAIN currReqState) \ {r} |-> currReqState[x]],
     dur   |-> [x \in (DOMAIN currDuration) \ {r} |-> currDuration[x]]]

\* HELPER: Attempt Acquire with Shedding
\* Returns record with new state and dropped flag
AttemptAcquire(r, type, currPool, currWait, currReqState) ==
    IF currPool[type] > 0 THEN
        \* Success: Get ticket
        [pool     |-> [currPool EXCEPT ![type] = @ - 1],
         wait     |-> currWait,
         reqState |-> [currReqState EXCEPT ![r] = IF type="Short" THEN "RunningShort" ELSE "RunningLong"],
         dropped  |-> FALSE]
    ELSE IF Cardinality(currWait[type]) < (IF type="Short" THEN ShortWaitLimit ELSE LongWaitLimit) THEN
        \* Wait: Enter queue
        [pool     |-> currPool,
         wait     |-> [currWait EXCEPT ![type] = @ \cup {r}],
         reqState |-> [currReqState EXCEPT ![r] = IF type="Short" THEN "WaitingShort" ELSE "WaitingLong"],
         dropped  |-> FALSE]
    ELSE
        \* Shed: Return dropped=TRUE (Caller handles cleanup)
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
RECURSIVE Pow(_, _)
Pow(b,e) == IF e = 0 THEN 1 ELSE b * Pow(b, e-1)

\* Scale factor for integer-scaled probabilities (parts-per-million)
ScaleFactor == 1000000

\* Integer floor division (safe for scaled usage): returns q in 0..ScaleFactor such that b*q <= a < b*(q+1)
FloorDiv(a,b) == IF b = 0 THEN 0 ELSE CHOOSE q \in 0..ScaleFactor : b*q <= a /\ a < b*(q+1)

\* Compute scaled Fraction: floor(scale * (pct/100)^e) without large intermediates
RECURSIVE ScaledPow(_, _, _)
ScaledPow(s, pct, e) == IF e = 0 THEN s ELSE ScaledPow(FloorDiv(s * pct, 100), pct, e-1)

CountRunning(type) ==
    Cardinality({ r \in DOMAIN requestState :
                    requestState[r] = (IF type = "Short" THEN "RunningShort" ELSE "RunningLong") })

RecordStats(newDrops) ==
    /\ step' = step + 1
    /\ cumulativeDrops' = [Short |-> cumulativeDrops.Short + (IF newDrops.Short THEN 1 ELSE 0),
                           Long  |-> cumulativeDrops.Long  + (IF newDrops.Long THEN 1 ELSE 0)]
    /\ LET shortRun == CountRunning("Short")
           longRun  == CountRunning("Long")
           shortScaled == ScaledPow(ScaleFactor, IOPercentage, shortRun)
           longScaled  == ScaledPow(ScaleFactor, IOPercentage, longRun)
       IN
       IF SampleInterval > 0 /\ (step' % SampleInterval = 0) THEN
           /\ sampleCount' = sampleCount + 1
           /\ totalShortWasteScaled' = totalShortWasteScaled + shortScaled
           /\ totalLongWasteScaled' = totalLongWasteScaled + longScaled
           /\ totalShortWasteNum' = totalShortWasteNum
           /\ totalShortWasteDen' = totalShortWasteDen
           /\ totalLongWasteNum' = totalLongWasteNum
           /\ totalLongWasteDen' = totalLongWasteDen
       ELSE
           /\ sampleCount' = sampleCount
           /\ totalShortWasteScaled' = totalShortWasteScaled
           /\ totalLongWasteScaled' = totalLongWasteScaled
           /\ totalShortWasteNum' = totalShortWasteNum
           /\ totalShortWasteDen' = totalShortWasteDen
           /\ totalLongWasteNum' = totalLongWasteNum
           /\ totalLongWasteDen' = totalLongWasteDen

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
                   /\ RecordStats([Short |-> TRUE, Long |-> FALSE])
               ELSE
                   \* Accepted: Commit new state
                   /\ ticketPool'   = outcome.pool
                   /\ waitSets'     = outcome.wait
                   /\ requestState' = outcome.reqState
                   /\ duration'     = newDuration
                   /\ nextReqId'    = nextReqId + 1
                   /\ RecordStats([Short |-> FALSE, Long |-> FALSE])
       ELSE
           \* CASE B: No Arrival (The "Clock Tick")
           \* Crucial: We must still advance the step and log the state
           /\ UNCHANGED <<ticketPool, waitSets, requestState, duration, nextReqId>>
           /\ RecordStats([Short |-> FALSE, Long |-> FALSE])

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
       \* Remove 'r' from the state maps completely
       /\ requestState' = clean.state
       /\ duration'     = clean.dur
       /\ nextReqId'    = nextReqId
       /\ RecordStats([Short |-> FALSE, Long |-> FALSE])

\* ACTION 3: Short Yield
ShortYieldToLong(r) ==
    /\ step < MaxSteps
    /\ requestState[r] = "RunningShort"
    /\ duration[r] > 10
    /\ LET relRes == ReleaseTicket("Short", ticketPool, waitSets, requestState)
           acqRes == AttemptAcquire(r, "Long", relRes.pool, relRes.wait, relRes.reqState) 
       IN
       IF acqRes.dropped THEN
            \* Dropped during transition: Garbage collect
            LET clean == RemoveRequest(r, acqRes.reqState, duration) IN
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = clean.state
            /\ duration'     = clean.dur
            /\ nextReqId'    = nextReqId
            /\ RecordStats([Short |-> FALSE, Long |-> TRUE])
       ELSE
            \* Successful transition
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = acqRes.reqState
            /\ duration'     = [duration EXCEPT ![r] = @ - 10]
            /\ nextReqId'    = nextReqId
            /\ RecordStats([Short |-> FALSE, Long |-> FALSE])

\* ACTION 4: Long Yield Loop
LongYieldLoop(r) ==
    /\ step < MaxSteps
    /\ requestState[r] = "RunningLong"
    /\ duration[r] > 10
    /\ LET relRes == ReleaseTicket("Long", ticketPool, waitSets, requestState)
           acqRes == AttemptAcquire(r, "Long", relRes.pool, relRes.wait, relRes.reqState) 
       IN
       IF acqRes.dropped THEN
            \* Dropped during loop: Garbage collect
            LET clean == RemoveRequest(r, acqRes.reqState, duration) IN
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = clean.state
            /\ duration'     = clean.dur
            /\ nextReqId'    = nextReqId
            /\ RecordStats([Short |-> FALSE, Long |-> TRUE])
       ELSE
            \* Successful re-entry
            /\ ticketPool'   = acqRes.pool
            /\ waitSets'     = acqRes.wait
            /\ requestState' = acqRes.reqState
            /\ duration'     = [duration EXCEPT ![r] = @ - 10]
            /\ nextReqId'    = nextReqId
            /\ RecordStats([Short |-> FALSE, Long |-> FALSE])

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
        /\ IF CSVRecords(CSVFile) = 0 THEN CSVWrite("%s", << "step,shortDrops,longDrops,samples,shortWasteNum,shortWasteDen,longWasteNum,longWasteDen,shortWasteScaledSum,longWasteScaledSum" >>, CSVFile) ELSE TRUE
        /\ CSVWrite("%s,%s,%s,%s,%s,%s,%s,%s,%s,%s", << step, cumulativeDrops.Short, cumulativeDrops.Long, sampleCount, 
                       totalShortWasteNum, totalShortWasteDen, totalLongWasteNum, 
                       totalLongWasteDen, totalShortWasteScaled, totalLongWasteScaled >>, CSVFile)
        /\ IOExec(<<"/usr/bin/env", "Rscript", "visualize_drops.R", CSVFile>>).exitValue = 0
        /\ FALSE
    ELSE TRUE

Spec == Init /\ [][Next]_Vars

=============================================================================
rm *.csv ; tlc ECSSim -note -generate -depth -1

-depth -1 for going until execution done 
-depth 100 for going for 100 steps

