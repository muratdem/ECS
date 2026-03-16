----------------------- MODULE MLFQ -----------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Jobs,           \* The set of model processes (e.g., {"A", "B"}
    Priorities,     \* The set of queue levels (e.g., 1..3, where 1 is High)
    TimeAllotment,  \* Function defining total time allowed per queue before demotion
    Quantum,        \* Function defining time slice length per queue
    BoostInterval,  \* The 'S' parameter for global priority boost
    MaxTime         \* Simulation limit

VARIABLES 
    (* The current priority queue for each job *)
    job_priority,
    (* Time used in current queue (for Rule 4 demotion) *)
    job_allotment_used,
    (* Time used in current time slice (for Rule 2 RR) *)
    job_quantum_used,
    (* Explicit queues to handle Round Robin ordering *)
    queues,
    (* Simulation clock and boost timer *)
    global_time,
    time_since_boost

vars == <<job_priority, job_allotment_used, job_quantum_used, queues, global_time, time_since_boost>>

(* Helper: Highest priority level (1 is highest, N is lowest) *)
TopPriority == 1
LowPriority == Cardinality(Priorities)

-----------------------------------------------------------------------------
(* OPERATORS & HELPERS *)

(* Convert a Set to a Sequence (for initialization) *)
RECURSIVE SetToSeq(_)
SetToSeq(S) == 
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE y \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

(* Rule 1: If Priority(A) > Priority(B), A runs. [4, 5] *)
(* We find the highest priority queue that is not empty. *)
HighestReadyQueue == 
    IF \E p \in Priorities : queues[p] /= <<>>
    THEN CHOOSE p \in Priorities : 
            /\ queues[p] /= <<>>
            /\ \A p2 \in Priorities : (p2 < p) => queues[p2] = <<>>
    ELSE 0 (* 0 Indicates system is idle/empty *)

-----------------------------------------------------------------------------
(* ACTIONS *)

(* INITIALIZATION *)
(* Rule 3: When a job enters the system, it is placed at the highest priority. [2, 3] *)
Init ==
    /\ job_priority = [j \in Jobs |-> TopPriority]
    /\ job_allotment_used = [j \in Jobs |-> 0]
    /\ job_quantum_used = [j \in Jobs |-> 0]
    (* All jobs start in the TopPriority queue sequence in arbitrary order *)
    /\ queues = [p \in Priorities |-> IF p = TopPriority THEN SetToSeq(Jobs) ELSE <<>>]
    /\ global_time = 0
    /\ time_since_boost = 0

(* Rule 5: After time period S, move all jobs to topmost queue. [2, 6] *)
BoostPriority ==
    /\ time_since_boost >= BoostInterval
    /\ queues' = [p \in Priorities |-> 
        IF p = TopPriority 
        THEN SetToSeq(Jobs) (* Everyone moves to Top *)
        ELSE <<>>]
    /\ job_priority' = [j \in Jobs |-> TopPriority]
    /\ job_allotment_used' = [j \in Jobs |-> 0] (* Reset accounting *)
    /\ job_quantum_used' = [j \in Jobs |-> 0]
    /\ time_since_boost' = 0
    /\ global_time' = global_time (* Boost happens instantaneously *)

(* Rule 4: Demotion. Once allotment is used, priority is reduced. [1, 2] *)
(* Note: We check this BEFORE running the job to enforce limits strictly. *)
DemoteJob ==
    LET p == HighestReadyQueue
    IN 
    /\ time_since_boost < BoostInterval
    /\ p > 0 (* There is a job to run *)
    /\ LET current_job == Head(queues[p]) IN
       (* Check if allotment exceeded *)
       /\ job_allotment_used[current_job] >= TimeAllotment[p]
       /\ p < LowPriority (* Can't go lower than bottom *)
       /\ job_priority' = [job_priority EXCEPT ![current_job] = p + 1]
       /\ job_allotment_used' = [job_allotment_used EXCEPT ![current_job] = 0]
       /\ job_quantum_used' = [job_quantum_used EXCEPT ![current_job] = 0]
       (* Move from Head of queue p to Tail of queue p+1 *)
       /\ queues' = [queues EXCEPT 
                        ![p] = Tail(queues[p]), 
                        ![p+1] = Append(queues[p+1], current_job)]
       /\ UNCHANGED <<global_time, time_since_boost>>

(* Rule 2: Round Robin. If quantum expired, rotate to back of SAME queue. [2, 4] *)
RotateRR ==
    LET p == HighestReadyQueue
    IN
    /\ time_since_boost < BoostInterval
    /\ p > 0
    /\ LET current_job == Head(queues[p]) IN
       (* Condition: Allotment NOT finished, but Quantum IS finished *)
       /\ job_allotment_used[current_job] < TimeAllotment[p]
       /\ job_quantum_used[current_job] >= Quantum[p]
       (* Action: Reset quantum, move to back of queue *)
       /\ job_quantum_used' = [job_quantum_used EXCEPT ![current_job] = 0]
       /\ queues' = [queues EXCEPT ![p] = Append(Tail(queues[p]), current_job)]
       /\ UNCHANGED <<job_priority, job_allotment_used, global_time, time_since_boost>>

(* Execution: Run the job at the head of the highest priority queue *)
RunJob ==
    LET p == HighestReadyQueue
    IN
    /\ time_since_boost < BoostInterval
    /\ global_time < MaxTime
    /\ p > 0
    /\ LET current_job == Head(queues[p]) IN
       (* Only run if we don't need to Demote (Rule 4) or Rotate (Rule 2) *)
       /\ job_allotment_used[current_job] < TimeAllotment[p]
       /\ job_quantum_used[current_job] < Quantum[p]
       (* Action: Progress time and usage counters *)
       /\ job_allotment_used' = [job_allotment_used EXCEPT ![current_job] = @ + 1]
       /\ job_quantum_used' = [job_quantum_used EXCEPT ![current_job] = @ + 1]
       /\ global_time' = global_time + 1
       /\ time_since_boost' = time_since_boost + 1
       /\ UNCHANGED <<job_priority, queues>>

(* Stop condition *)
Terminate == 
    /\ global_time >= MaxTime
    /\ UNCHANGED vars

(* Next State Relation *)
Next == 
    \/ BoostPriority
    \/ DemoteJob
    \/ RotateRR
    \/ RunJob
    \/ Terminate

Spec == Init /\ [][Next]_vars


(* ========================================================================= *)
(* SIMULATION PARAMETERS to define the "Tuning" values                       *)
(* ========================================================================= *)

(* 
   Defines time slices (Quantum) per queue (Source [1]).
   Queue 1 (High): 10 ticks (Interactive, quick response)
   Queue 2 (Mid):  20 ticks
   Queue 3 (Low):  40 ticks (Batch, high throughput)
*)
MC_Quantum == 
    [p \in {1,2,3} |-> IF p=1 THEN 10 ELSE IF p=2 THEN 20 ELSE 40]

(* 
   Defines Allotment: Total time allowed in a queue before demotion (Rule 4).
   We set this to 2x the Quantum to allow a job to rotate Round-Robin 
   at least once before being demoted.
*)
MC_TimeAllotment == 
    [p \in {1,2,3} |-> IF p=1 THEN 20 ELSE IF p=2 THEN 40 ELSE 80]


=============================================================================
To run the MLFQ TLA+ model at Spectacle for visualization:
https://will62794.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmuratdem%2FECS%2Frefs%2Fheads%2Fmain%2FMLFQ.tla&initPred=Init&nextPred=Next&constants%5BJobs%5D=%7B%22A%22%2C%20%22B%22%7D&constants%5BPriorities%5D=1..3&constants%5BTimeAllotment%5D=%3C%3C2%2C%204%2C%208%3E%3E&constants%5BQuantum%5D=%3C%3C1%2C%202%2C%204%3E%3E&constants%5BBoostInterval%5D=5&constants%5BMaxTime%5D=20&explodedConstantExpr=Jobs
 

