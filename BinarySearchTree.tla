-------------------------- MODULE BinarySearchTree --------------------------
EXTENDS Naturals, Sequences, Integers, FiniteSets, Randomization

(* --constants and variables-- *)
FNat == 0..7 \* Finite set of natural numbers
FNatNil  == FNat \union {-1} \* Extended set including a special nil value (-1)

(* --state variables-- *)
VARIABLE root, nodes, parent, left, right \* State variables representing the tree structure

(* --TypeOK-- *)
TypeOK == 
    /\ (root = -1 \/ root \in FNat)  \* Root is either -1 (empty) or a valid node
    /\ nodes \subseteq FNat \* All nodes are within the finite set of natural numbers
    /\ parent \in [FNat -> FNatNil] \* Parent mapping: each node maps to a parent or -1
    /\ left \in [FNat -> FNatNil] \* Left child mapping
    /\ right \in [FNat -> FNatNil] \* Right child mapping
    
(* --initial state-- *)
Init == 
    /\ root = -1  \* Tree is initially empty
    /\ nodes = {} \* No nodes in the tree initially
    /\ parent = [n \in FNat |-> -1 ] \* All nodes initially have no parent
    /\ left = [n \in FNat |-> -1 ] \* No left children initially
    /\ right = [n \in FNat |-> -1 ]  \* No right children initially

(* --insert operation-- *)
RECURSIVE InsertHelper(_, _)
InsertHelper(n, cur) ==
    (* Recursive helper function for insertion. *)
    (* If the current node (cur) is the node to insert (n), nothing changes. *)
    (* Otherwise, find the correct position to insert the new node. *)
     IF n = cur
     THEN UNCHANGED <<root, nodes, parent, left, right>>
     ELSE 
        IF n < cur
        THEN
            IF left[cur] = -1
            THEN 
                /\ nodes' = nodes \union {n}
                /\ parent' = [parent EXCEPT ![n] = cur]
                /\ left' = [left EXCEPT ![cur] = n]
                /\ UNCHANGED << root, right>>
            ELSE 
                InsertHelper(n, left[cur])
        ELSE 
            IF right[cur] = -1
            THEN 
                /\ nodes' = nodes \union {n}
                /\ parent' = [parent EXCEPT ![n] = cur]
                /\ right' = [right EXCEPT ![cur] = n]
                /\ UNCHANGED <<root, left>>
            ELSE 
                InsertHelper(n, right[cur])  

Insert (n) == 
    (* Main insertion function. *)
    (* If n is not in nodes and is a valid number, perform insertion. *)
    (* Start insertion from the root. *)
    /\ n \notin nodes 
    /\ n \in FNat
    /\ IF root = -1
       THEN 
           /\ root' = n 
           /\ nodes' = {n}
           /\ UNCHANGED << parent, left, right>>
       ELSE InsertHelper(n, root)

(* --find operation-- *)
RECURSIVE Find(_, _)
Find (n, cur) == 
    (* Recursive function to find a node in the tree. *)
    (* If current node (cur) is -1 or matches n, return the result. *)
    (* Otherwise, search left or right subtree based on comparison. *)
    IF cur = -1 
    THEN -1
    ELSE 
        IF n = cur
        THEN n
        ELSE 
            IF n < cur
            THEN Find(n, left[cur])
            ELSE Find(n, right[cur])
            
(* --DeleteHelper-- *)
RECURSIVE DeleteHelper(_)
DeleteHelper(node) == 
    \* This function handles the deletion of a node from the binary search tree.
    \* It considers different cases based on the number and position of children of the node.
    
    \* Case 1: The node has no child.
    IF left[node] = -1 /\ right[node] = -1 
    THEN
        /\ nodes' = nodes \ {node} \* Remove the node from the set of nodes.
        /\ IF node = root \* If the node is the root, set root to -1 (empty tree).
           THEN /\ root' = -1
                /\ UNCHANGED << left, right, parent >>
                
           \* If the node is a left child of its parent.
           ELSE 
                IF left[parent[node]] = node 
                THEN /\ left' = [left EXCEPT ![parent[node]] = -1] \* Remove the node from the left child of its parent.
                     /\ parent' = [parent EXCEPT ![node] = -1]  \* Update the parent mapping.
                     /\ UNCHANGED << right, root >>
                     
                \* If the node is a right child of its parent.
                ELSE
                    IF right[parent[node]] = node
                    THEN 
                        \* Remove the node from the right child of its parent.
                        /\ right' = [right EXCEPT ![parent[node]] = -1]
                        /\ parent' = [parent EXCEPT ![node] = -1] 
                        /\ UNCHANGED <<left, root>>
                    \* if the node is not a child
                    ELSE UNCHANGED <<root, nodes, parent, left, right>>
    
    \* Case 2: The node has exactly one child.  
    ELSE
         IF ((right[node] = -1 \/ left[node] = -1) /\ \neg(right[node] = -1 /\ left[node] = -1))
        THEN 
            \* If the node has a right child but no left child.
            IF (right[node] /= -1 /\ left[node] = -1)  
            THEN 
               
               \* if the node is a left child 
               IF  parent[node] /= -1 /\ left[parent[node]] = node
               THEN
                    \* update the mapping and remove the node 
                    /\ left' = [left EXCEPT ![parent[node]] = right[node], ![node] = -1]
                    /\ parent' = [parent EXCEPT ![node] = -1, ![right[node]] = parent[node]]
                    /\ right' = [right EXCEPT ![node] = -1]
                    /\ nodes' = nodes \ {node}
                    /\ UNCHANGED <<root>>  
               \* if the node is a right child
               ELSE  
                    IF parent[node] /= -1 /\ right[parent[node]] = node
                    THEN
                      \* update the mapping and remove the node
                      /\ right' = [right EXCEPT ![parent[node]] = right[node], ![node] = -1]
                      /\ parent' = [parent EXCEPT ![node] = -1, ![right[node]] = parent[node]]
                      /\ left' = [left EXCEPT ![node] = -1]
                      /\ nodes' = nodes \ {node}
                      /\ UNCHANGED <<root>>
                    ELSE UNCHANGED <<root, nodes, parent, left, right>>     

            \* the node has left child but no right child      
            ELSE   
                IF (right[node] = -1 /\ left[node] /= -1)
                THEN 
                   \* if the node is a left child 
                   IF parent[node] /= -1 /\ left[parent[node]] = node
                   THEN 
                      \* update the mapping and remove the node
                      /\ left' = [left EXCEPT ![parent[node]] = left[node], ![node] = -1]
                      /\ parent' = [parent EXCEPT ![node] = -1, ![left[node]] = parent[node]]
                      /\ right' = [right EXCEPT ![node] = -1]
                      /\ nodes' = nodes \ {node}
                      /\ UNCHANGED <<root>> 
                      
                   \* if the node is a right child
                   ELSE
                        IF parent[node] /= -1 /\ right[parent[node]] = node
                        THEN 
                          \* update the mapping and remove the node
                          /\ right' = [right EXCEPT ![parent[node]] = left[node], ![node] = -1]
                          /\ left' = [left EXCEPT ![node] = -1]
                          /\ parent' = [parent EXCEPT ![node] = -1, ![left[node]] = parent[node]]
                          /\ nodes' = nodes \ {node}
                          /\ UNCHANGED <<root>>    
                        ELSE UNCHANGED <<root, nodes, parent, left, right>>
                ELSE UNCHANGED <<root, nodes, parent, left, right>>
        
        \* this part is for future work, should be the case that the node has 2 children, which might need recursive update  
        ELSE UNCHANGED <<root, nodes, parent, left, right>> 

(* --delete operation-- *)
Delete(n) == 
    (* Main deletion function. *)
    (* Only deletes if n is in the tree and the tree is not empty. *)
    IF Find (n, root) = -1 \/ nodes = {}
    THEN UNCHANGED <<root, nodes, parent, left, right>>
    ELSE DeleteHelper(Find(n, root))

(* invariants-------------------*)

\* Bi-relationship
\* if a node A is a child of node B, then B must be parent of node A
BiRelationship ==  
    \A n \in nodes: (\E n1 \in nodes:
        (n /= n1 /\ parent[n] = n1) => (n = left[n1] \/ n = right[n1])) 

\* root can reach anyone in the set node
RECURSIVE IsReachable(_, _)
IsReachable(cur, n) ==
    IF cur = -1
    THEN FALSE
    ELSE IF cur = n
         THEN TRUE
         ELSE IsReachable(left[cur], n) \/ IsReachable(right[cur], n)

\* all node should be reachable from root
ReachableInvariant == 
    \A n \in nodes:
        \/ IsReachable(root, n)
        \/ root = -1  

\* the tree should be sorted (using Traverse)
RECURSIVE TraverseRecursive(_)
TraverseRecursive(cur) ==
    IF cur = -1
    THEN <<>>
    ELSE 
        LET leftSeq == TraverseRecursive(left[cur])
            rightSeq == TraverseRecursive(right[cur])
        IN Append(leftSeq, cur) \o rightSeq

IsSorted(seq) == \A i,j \in 1..Len(seq) : (i < j) => seq[i] < seq[j]

SortInvariant == 
    \/ Cardinality(nodes) <= 1
    \/ IsSorted(TraverseRecursive(root))                             

(* Invariants *)
Invariants == 
    /\ TypeOK
    /\ BiRelationship
    /\ ReachableInvariant
    /\ SortInvariant

(* Next *)       
Next == 
    \E n \in FNat: 
       \/ Insert(n)
       \/ Delete(n)
       
Spec == Init /\ [][Next]_<<root, nodes,parent,left,right>>

=============================================================================
\* Modification History
\* Last modified Wed Dec 06 21:47:10 EST 2023 by choujordan
\* Created Tue Nov 28 15:28:01 EST 2023 by choujordan
