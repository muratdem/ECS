--------------------------- MODULE ECS ---------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Requests,           \* The set of all possible request identifiers
    ShortTickets,       \* Capacity of short ticket pool (e.g., 5)
    LongTickets         \* Capacity of long ticket pool (e.g., 1)

VARIABLES
    requestState,       \* Function: Request -> State Enum
    ticketPool,         \* Function: {Short, Long} -> Integer (available tickets)
    waitSets            \* Function: {Short, Long} -> Set of Requests

\* State Enums
States == {
    "Idle",             \* Not in system
    "WaitingShort",     \* Waiting for a short ticket
    "RunningShort",     \* Holding a short ticket
    "WaitingLong",      \* Waiting for a long ticket
    "RunningLong",      \* Holding a long ticket
    "Completed"         \* Finished and exited
}

TicketTypes == {"Short", "Long"}

Vars == <<requestState, ticketPool, waitSets>>

-----------------------------------------------------------------------------

\* Type Invariant: Ensures tickets are conserved and state is valid
TypeOK ==
    /\ requestState \in [Requests -> States]
    /\ ticketPool \in [TicketTypes -> Nat]
    /\ waitSets \in [TicketTypes -> SUBSET Requests]
    /\ \A t \in TicketTypes : ticketPool[t] <= (IF t="Short" THEN ShortTickets ELSE LongTickets)

-----------------------------------------------------------------------------

\* Initial State: All requests are Idle, pools are full, wait sets empty
Init ==
    /\ requestState = [r \in Requests |-> "Idle"]
    /\ ticketPool   = [Short |-> ShortTickets, Long |-> LongTickets]
    /\ waitSets     = [Short |-> {}, Long |-> {}]

-----------------------------------------------------------------------------

\* HELPER: Logic to acquire a ticket of 'type' for request 'r'
\* Returns the new state of (ticketPool, waitSets, requestState)
AttemptAcquire(r, type, currPool, currWait, currReqState) ==
    IF currPool[type] > 0
    THEN
        \* Success: Decrement pool, Enter Running state
        << [currPool EXCEPT ![type] = @ - 1],
           currWait,
           [currReqState EXCEPT ![r] = IF type="Short" THEN "RunningShort" ELSE "RunningLong"] >>
    ELSE
        \* Failure: Enter Wait Set
        << currPool,
           [currWait EXCEPT ![type] = @ \cup {r}],
           [currReqState EXCEPT ![r] = IF type="Short" THEN "WaitingShort" ELSE "WaitingLong"] >>

\* HELPER: Logic to release a ticket of 'type'
\* If waiters exist, hand off to one (non-deterministically). If not, increment pool.
ReleaseTicket(type, currPool, currWait, currReqState) ==
    IF currWait[type] /= {}
    THEN
        \* Handoff: Pick a waiter non-deterministically
        LET waiter == CHOOSE w \in currWait[type] : TRUE
        IN
            << currPool,
               [currWait EXCEPT ![type] = @ \ {waiter}],
               \* Waiter wakes up and starts running
               [currReqState EXCEPT ![waiter] = IF type="Short" THEN "RunningShort" ELSE "RunningLong"] >>
    ELSE
        \* No waiters: Return ticket to pool
        << [currPool EXCEPT ![type] = @ + 1],
           currWait,
           currReqState >>

-----------------------------------------------------------------------------

\* ACTION 1: Request Arrival
\* A new request enters and tries to get a Short Ticket.
RequestArrival(r) ==
    /\ requestState[r] = "Idle"
    /\ LET outcome == AttemptAcquire(r, "Short", ticketPool, waitSets, requestState) IN
       /\ ticketPool'   = outcome[1]
       /\ waitSets'     = outcome[2]
       /\ requestState' = outcome[3]

\* ACTION 2: Task Completion
\* A task (Short or Long) finishes execution within its 10ms slice.
\* It releases its ticket and exits.
Complete(r) ==
    /\ requestState[r] \in {"RunningShort", "RunningLong"}
    /\ LET type == IF requestState[r] = "RunningShort" THEN "Short" ELSE "Long"
       IN
       \* 1. Mark 'r' as Completed
       \* 2. Release the ticket (triggering handoff if needed)
       LET releaseOutcome == ReleaseTicket(type, ticketPool, waitSets, requestState) IN
           /\ ticketPool' = releaseOutcome[1]
           /\ waitSets'   = releaseOutcome[2]
           \* Important: The release helper updates the WAITER'S state. We must also update 'r'.
           \* If the release picked a waiter, requestState' has that waiter as Running.
           \* We superimpose setting 'r' to Completed.
           /\ requestState' = [releaseOutcome[3] EXCEPT ![r] = "Completed"]

\* ACTION 3: Short Yield (Promotion)
\* A Short task runs for 10ms without finishing.
\* It releases the Short Ticket and attempts to acquire a Long Ticket.
ShortYieldToLong(r) ==
    /\ requestState[r] = "RunningShort"
    \* Step A: Release Short Ticket
    /\ LET releaseOutcome == ReleaseTicket("Short", ticketPool, waitSets, requestState)
           poolAfterRelease == releaseOutcome[1]
           waitAfterRelease == releaseOutcome[2]
           reqStateAfterRelease == releaseOutcome[3]
       IN
       \* Step B: Attempt to Acquire Long Ticket
       \* We try to acquire Long using the state resulting from Step A
       LET acquireOutcome == AttemptAcquire(r, "Long", poolAfterRelease, waitAfterRelease, reqStateAfterRelease)
       IN
           /\ ticketPool'   = acquireOutcome[1]
           /\ waitSets'     = acquireOutcome[2]
           /\ requestState' = acquireOutcome[3]

\* ACTION 4: Long Yield (Looping)
\* A Long task runs for 10ms without finishing.
\* It releases the Long Ticket and immediately attempts to re-acquire it.
LongYieldLoop(r) ==
    /\ requestState[r] = "RunningLong"
    \* Step A: Release Long Ticket
    /\ LET releaseOutcome == ReleaseTicket("Long", ticketPool, waitSets, requestState)
           poolAfterRelease == releaseOutcome[1]
           waitAfterRelease == releaseOutcome[2]
           reqStateAfterRelease == releaseOutcome[3]
       IN
       \* Step B: Attempt to Re-Acquire Long Ticket
       LET acquireOutcome == AttemptAcquire(r, "Long", poolAfterRelease, waitAfterRelease, reqStateAfterRelease)
       IN
           /\ ticketPool'   = acquireOutcome[1]
           /\ waitSets'     = acquireOutcome[2]
           /\ requestState' = acquireOutcome[3]

-----------------------------------------------------------------------------

\* Next State Relation
\* Written in canonical form to keep Spectacle visualization happy
Next ==
        \/ \E r \in Requests : RequestArrival(r)
        \/ \E r \in Requests : Complete(r)
        \/ \E r \in Requests : ShortYieldToLong(r)
        \/ \E r \in Requests : LongYieldLoop(r)

\* Specification with Fairness to ensure the system makes progress
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

=============================================================================