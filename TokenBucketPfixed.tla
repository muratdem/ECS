----------------------- MODULE TokenBucketPfixed -----------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS 
    MaxRetries, 
    BucketCapacity, 
    SuccessReward, 
    RetryCost

(* --algorithm TokenBucket
variables
    bucket = BucketCapacity,
    \* A queue of incoming requests to process
    requests = << "R1", "R2", "R3" >>, 
    processed_count = 0;

fair process ClientDriver = "DriverThread"
variables 
    req_idx = 1,
    tries = 0,
    server_succeeds = FALSE;
begin
    DriverLoop:
    while req_idx <= Len(requests) do
        tries := 0;
        
        Attempt:
        while tries <= MaxRetries do
            \* Non-deterministic server response
            with s \in {TRUE, FALSE} do
                server_succeeds := s;
            end with;

            ProcessResponse:
            if server_succeeds then
                \* Success: Refill bucket and move to next request
                bucket := IF bucket + SuccessReward > BucketCapacity 
                          THEN BucketCapacity 
                          ELSE bucket + SuccessReward;
                goto NextRequest;
            else
                \* Failure: Prepare to retry
                tries := tries + 1;
                
                if tries <= MaxRetries then
                    \* THE FIX: Fail-fast and drop
                    if bucket >= RetryCost then
                        bucket := bucket - RetryCost;
                    else
                        goto NextRequest; \* Drop it and unblock the queue!
                    end if;
                end if;
            end if;
        end while;

        NextRequest:
        processed_count := processed_count + 1;
        req_idx := req_idx + 1;
    end while;
end process;
end algorithm; *)

------------------------------------------------------------------------------

\* BEGIN TRANSLATION (chksum(pcal) = "ac47fa01" /\ chksum(tla) = "b522c930")
VARIABLES pc, bucket, requests, processed_count, req_idx, tries, 
          server_succeeds

vars == << pc, bucket, requests, processed_count, req_idx, tries, 
           server_succeeds >>

ProcSet == {"DriverThread"}

Init == (* Global variables *)
        /\ bucket = BucketCapacity
        /\ requests = << "R1", "R2", "R3" >>
        /\ processed_count = 0
        (* Process ClientDriver *)
        /\ req_idx = 1
        /\ tries = 0
        /\ server_succeeds = FALSE
        /\ pc = [self \in ProcSet |-> "DriverLoop"]

DriverLoop == /\ pc["DriverThread"] = "DriverLoop"
              /\ IF req_idx <= Len(requests)
                    THEN /\ tries' = 0
                         /\ pc' = [pc EXCEPT !["DriverThread"] = "Attempt"]
                    ELSE /\ pc' = [pc EXCEPT !["DriverThread"] = "Done"]
                         /\ tries' = tries
              /\ UNCHANGED << bucket, requests, processed_count, req_idx, 
                              server_succeeds >>

Attempt == /\ pc["DriverThread"] = "Attempt"
           /\ IF tries <= MaxRetries
                 THEN /\ \E s \in {TRUE, FALSE}:
                           server_succeeds' = s
                      /\ pc' = [pc EXCEPT !["DriverThread"] = "ProcessResponse"]
                 ELSE /\ pc' = [pc EXCEPT !["DriverThread"] = "NextRequest"]
                      /\ UNCHANGED server_succeeds
           /\ UNCHANGED << bucket, requests, processed_count, req_idx, tries >>

ProcessResponse == /\ pc["DriverThread"] = "ProcessResponse"
                   /\ IF server_succeeds
                         THEN /\ bucket' = (IF bucket + SuccessReward > BucketCapacity
                                            THEN BucketCapacity
                                            ELSE bucket + SuccessReward)
                              /\ pc' = [pc EXCEPT !["DriverThread"] = "NextRequest"]
                              /\ tries' = tries
                         ELSE /\ tries' = tries + 1
                              /\ IF tries' <= MaxRetries
                                    THEN /\ IF bucket >= RetryCost
                                               THEN /\ bucket' = bucket - RetryCost
                                                    /\ pc' = [pc EXCEPT !["DriverThread"] = "Attempt"]
                                               ELSE /\ pc' = [pc EXCEPT !["DriverThread"] = "NextRequest"]
                                                    /\ UNCHANGED bucket
                                    ELSE /\ pc' = [pc EXCEPT !["DriverThread"] = "Attempt"]
                                         /\ UNCHANGED bucket
                   /\ UNCHANGED << requests, processed_count, req_idx, 
                                   server_succeeds >>

NextRequest == /\ pc["DriverThread"] = "NextRequest"
               /\ processed_count' = processed_count + 1
               /\ req_idx' = req_idx + 1
               /\ pc' = [pc EXCEPT !["DriverThread"] = "DriverLoop"]
               /\ UNCHANGED << bucket, requests, tries, server_succeeds >>

ClientDriver == DriverLoop \/ Attempt \/ ProcessResponse \/ NextRequest

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ClientDriver
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ClientDriver)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
