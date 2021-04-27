/* OneD
 * Author: matty
 * Creation date: 31/10/2019
 */
MACHINE OneD
DEFINITIONS SET_PREF_MAXINT == 32
VARIABLES s1, s2
INVARIANT s1:seq(NAT1) & s2:seq(NAT1)
INITIALISATION s1 := [1,2] || s2 := [1,1,3,2,2] /*Used for testing sequences. Here, s1 is the subsequence we are looking to find, and s2 is the main sequence.*/
OPERATIONS
    
oo <-- contiguous = 
    PRE s1:seq(NAT1) & s2:seq(NAT1) & card(s1) < card(s2)
    THEN
        IF
            #(nn).(nn:NAT1 & nn < size(s2)-size(s1) & s1=(s2\|/nn-1)/|\size(s1)) 
            /*Checks for the existence of a starting point n, where dropping all previous elements and taking the next consecutive elements up to the size of the sequence we are trying to find, results in the sequence.*/
        THEN
            oo := TRUE
        ELSE
            oo := FALSE
        END
    END;
    
oo <-- subsequence = 
    PRE s1 : seq(NAT1) & s2 : seq(NAT1) & card(s1) <= card(s2)
    THEN
        IF
            #(s3).(s3 : seq(NAT1) & size(s3) = size(s1) 
                 &!(xx,yy).((xx:dom(s3) & yy:dom(s3) & xx < yy) => (s3(xx) < s3(yy))) 
                 &!(zz).(zz:dom(s3) => s1(zz) = s2(s3(zz))))
            /*s3 represents a sequence that records the position of the s1 numbers in s2. We ensure that it is the same length s1, that the positions in s2 are ascending, and that the RHS of the numbers in s1 are the same as the numbers in s2 */
        THEN
            oo := TRUE
        ELSE
            oo := FALSE
        END
    END
END
