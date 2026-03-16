------------------------- MODULE TokenBucketDriver -------------------------
EXTENDS Integers

CONSTANTS 
    Requests,          \* Set of request IDs, e.g., { "R1", "R2", "R3" }
    MaxRetries,        \* Maximum times a single request can be retried
    BucketCapacity,    \* Maximum tokens the bucket can hold
    SuccessReward,     \* Tokens added upon a successful request (e.g., 1)
    RetryCost          \* Tokens consumed to attempt a retry (e.g., 10)

VARIABLES
    bucket,            \* Current tokens in the bucket
    reqState,          \* PENDING, IN_FLIGHT, FAILED, DONE, DROPPED
    tries              \* Number of attempts made per request

vars == <<bucket, reqState, tries>>

-----------------------------------------------------------------------------
\* INITIALIZATION
Init ==
    /\ bucket = BucketCapacity
    /\ reqState = [r \in Requests |-> "PENDING"]
    /\ tries = [r \in Requests |-> 0]


\* 1. Send a new request
Send(r) ==
    /\ reqState[r] = "PENDING"
    /\ reqState' = [reqState EXCEPT ![r] = "IN_FLIGHT"]
    /\ tries' = [tries EXCEPT ![r] = 1]
    /\ UNCHANGED <<bucket>>

\* 2. Server responds to an in-flight request (non-det Success/Failure)
ServerRespond(r) ==
    /\ reqState[r] = "IN_FLIGHT"
    /\ \/ \* Branch A: Server Success
          /\ reqState' = [reqState EXCEPT ![r] = "DONE"]
          /\ bucket' = IF bucket + SuccessReward > BucketCapacity 
                       THEN BucketCapacity 
                       ELSE bucket + SuccessReward
       \/ \* Branch B: Server Failure
          /\ reqState' = [reqState EXCEPT ![r] = "FAILED"]
          /\ UNCHANGED bucket
    /\ UNCHANGED <<tries>>

\* 3. Client retries a failed request
Retry(r) ==
    /\ reqState[r] = "FAILED"
    /\ tries[r] < MaxRetries
    /\ bucket >= RetryCost             \* Must have enough tokens to retry
    /\ reqState' = [reqState EXCEPT ![r] = "IN_FLIGHT"]
    /\ tries' = [tries EXCEPT ![r] = tries[r] + 1]
    /\ bucket' = bucket - RetryCost

\* 4. Client drops a request 
Drop(r) ==
    /\ reqState[r] = "FAILED"
    /\ \/ tries[r] >= MaxRetries    \* Drop if we hit the retry limit
       \/ bucket < RetryCost        \* Drop if out of tokens to retry 
    /\ reqState' = [reqState EXCEPT ![r] = "DROPPED"]
    /\ UNCHANGED <<bucket, tries>>

-----------------------------------------------------------------------------
Next == 
    \/ \E r \in Requests : Send(r) 
    \/ \E r \in Requests : ServerRespond(r) 
    \/ \E r \in Requests : Retry(r) 
    \/ \E r \in Requests : Drop(r)

\* Weak Fairness guarantees that if an action is continuously enabled, it will eventually happen.
\* This is required to check for Liveness (Starvation).
Fairness == \A r \in Requests : 
                /\ WF_vars(Send(r)) 
                /\ WF_vars(ServerRespond(r)) 
                /\ WF_vars(Retry(r)) 
                /\ WF_vars(Drop(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* PROPERTIES TO CHECK IN THE MODEL CHECKER

\* 1. Safety: A request never exceeds max retries
MaxRetriesRespected == \A r \in Requests : tries[r] <= MaxRetries

\* 2. LIVENESS (Starvation Freedom): Every request eventually finishes or is safely dropped.
\* If this fails, your client driver has a starvation/deadlock vulnerability.
NoStarvation == \A r \in Requests : <>(reqState[r] \in {"DONE", "DROPPED"})

=============================================================================
-coverage 1 -workers 6

-generate -depth -1
-depth -1 for going until execution done 
-depth 100 for going for 100 steps

To run the MLFQ TLA+ model at Spectacle for visualization:
https://will62794.github.io/spectacle/