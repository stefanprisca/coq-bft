----------------
Related work
---------------

The project is based on the "Practical Byzantine fault tolerance and proactive recovery." publication by Miguel et.al. [1].
The authors present an implementation of byzantine fault tolerant systems, which allows the system to resist BF as long as at most (n - 1)/3 out of a total of n replicas are faulty. Their work is based on previous replication algorithms (e.g. Paxos by Lamport), and extends those with BFT.
Replication is done using a primary backup mechanism (primary node) and quorums (groups of nodes) to order the incoming requests. A node is selected as primary node, and decides the order in which to execute requests.
Replicating a request is then a three stage process (Pre-Prepare, Prepare, Commit). In order to go from one stage to the other, nodes must obtain approval from a quorum (group of nodes).
In the end, a request can only be committed if there is a quorum which agrees on the ordering of all requests committed so far and on the sequence number assigned to this request.
Replicas operate in the context of a view. The primary decides the order of requests within the view. When the primary becomes faulty, the other replicas change the view in order to select a new primary.
The authors claim, and informally prove that the view change algorithm ensures liveness and safety (keep exact transaction record between changing views) of the system.

-----------------
 Problem analysis
-----------------

The condition for a system to have tolerance to BF is that, after processing a request all the non faulty replicas in the system have agreed to assign the same sequence number. In a primary-backup replication system, this sequence number corresponds to the one which the primary replica assigned. This can be stated as the following theorem:

[Theorem BFT] 
For a given request R, if the primary replica P assigns sequence number N, after replicating the request in the system all non faulty replicas assign sequence number N for R.

Miguel et.al. argue that their system achieves Byzantine Fault Tolerance under the condition that the majority of the replicas are non faulty. The system presented consists of 3*F+1 total replicas (F = number of faulty replicas). The condition under which a replica accept a given request is that it gathered 2*F+1 quorum votes from all the other replicas in the system. This means that 2*F+1 of the other replicas have agreed to assign the same sequence number to the request. 
Based on this, the Byzantine Fault Tolerance theorem holds if the quorum certified condition above holds. Knowing this, and knowing that the system has 2*F+1 non-faulty replicas (from above), the Quorum Certified Property can be stated as:

[Property QCertified]
A sequence number N is Quorum Certified for request R if at least all the other non-faulty replicas have assigned N to R.

Having the BFT Theorem and the QCertified property, it remains to prove that at the end of processing the request, the QCertified property holds for all replicas in the system, therefore the whole system will meet the condition of the BFT Theorem.

---------------
Notes
--------------
The local import <Require Import Maps.> comes from Software Foundations introduction in Coq.

----------
Bib
----------
[1] Castro, Miguel, and Barbara Liskov. "Practical Byzantine fault tolerance and proactive recovery." ACM Transactions on Computer Systems (TOCS) 20.4 (2002): 398-461.
