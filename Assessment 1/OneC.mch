/* OneC
 * Author: matty
 * Creation date: 08/11/2019
 */
MACHINE
    OneC(mmax)
CONSTRAINTS mmax:NAT1
VARIABLES record
INVARIANT record:(0..mmax)-->NAT
/*
    Original Initialisation creates an empty function. Record is a total function, and so every element should be mapped; changed to default to 0 as no marks have been assigned.
*/
INITIALISATION record := (0..mmax)*{0} 
/*
    Previous operation allowed assignment of a mark that was greater than the maximum mark. Now a mark may only be increased if it is below the maximum. 
*/
OPERATIONS
    addmark(mm) = 
        PRE
            mm:NAT
        THEN
            /*Had to also ensure the RHS of the function remains an element of NAT. All proofs now succeed.*/
            IF
                mm < mmax & record(mm) < MAXINT
            THEN
                record(mm):= record(mm)+1
            END
        END
END
