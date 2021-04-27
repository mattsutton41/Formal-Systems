/* Bag
 * Author: matty
 * Creation date: 06/11/2019
 */
MACHINE
    Bag
DEFINITIONS SET_PREF_MAXINT == 10
SETS ELEMENTS
CONSTANTS cap
PROPERTIES cap = 10
VARIABLES bag, cost
INVARIANT cap:NAT1 & bag:ELEMENTS+->NAT1 & cost:ELEMENTS-->NAT & !(xx).(xx:dom(bag)=>bag(xx)<= cap)
INITIALISATION bag:={} || cost:=ELEMENTS*{0}
OPERATIONS
    addbag(ee) = 
        PRE
            ee:ELEMENTS
        THEN
            IF 
                ee/:dom(bag) /*If ee is not an element in the bag we introduce it*/
            THEN
                bag:=bag\/{ee |-> 1}
            ELSE
                IF 
                    bag(ee)<cap /*ensures adding new element doesn't violate max bag size*/
                THEN
                    bag(ee):=bag(ee)+1
                ELSE
                    bag(ee):=bag(ee)
                END
            END
    END;

    rembag(ee) = /*First checks case where item is removed altogether to avoid assignment to 0*/
        PRE
            ee:ELEMENTS & ee:dom(bag)
        THEN
            IF
                bag(ee)=1
            THEN
                bag:=bag-{ee |-> 1}
            ELSE
                bag(ee):=bag(ee)-1
            END
    END;
 
    oo <-- countelm(ee) = /*Have to avoid the lack of 0 assignment in partial function*/
        PRE
            ee : ELEMENTS
        THEN
            IF
                ee : dom(bag)
            THEN
                oo := bag(ee)
            ELSE
                oo := 0
            END
    END;

    oo <-- totelms =
        oo:=SIGMA(xx).(xx:dom(bag)|bag(xx));

    bb <-- isin(ee) = /*Simple boolean check for appearance of element in domain*/
        PRE
            ee:ELEMENTS
        THEN
            IF
                ee:dom(bag)
            THEN
                bb:=TRUE
            ELSE
                bb:=FALSE
            END
    END;

    bagunion(bb) =
        PRE
            bb:ELEMENTS+->NAT1 & bb/={} & max(ran(bb))<=cap
        THEN
            ANY xx /*Non-deterministically select a bag fitting the constraints*/
            WHERE ((xx : ELEMENTS +-> NAT1) 
                    & dom(xx)=dom(bag)\/dom(bb) 
                    & !(yy).(yy:ELEMENTS & yy:dom(bag) & yy/:dom(bb) => xx(yy)=bag(yy)) /*if element isn't in new bag, don't change value*/
                    & !(yy).(yy:ELEMENTS & yy/:dom(bag) & yy:dom(bb) => xx(yy)=bb(yy)) /*if element isn't in bag, take value in new bag*/
                    & !(yy).(yy:ELEMENTS & yy:dom(bag) & yy:dom(bb) &(bag(yy)+bb(yy)<=cap) => xx(yy)=bag(yy)+bb(yy))/*if element is in both bags, sum them */
                    & !(yy).(yy:ELEMENTS & yy:dom(bag) & yy:dom(bb) &(bag(yy)+bb(yy)>cap) => xx(yy)=cap))
            THEN bag := xx
            END
    END;
    
    ss <-- outputseq =
            BEGIN
                ANY xx /*Non-deterministically select a sequence containing each element as many times as it occurs in the bag*/
                WHERE (xx:seq(ELEMENTS)
                      & size(xx) = SIGMA(xx).(xx:ran(bag)|xx*card(bag|>{xx}))/*Sequence is of correct length*/
                      & !(yy).(yy:dom(bag) => card(xx|>{yy}) = bag(yy)))/*Each element is represented the correct number of times*/
                THEN ss := xx
                END
    END;
    
    addinseq(ss) = 
        PRE
            ss : seq(ELEMENTS)
        THEN
            ANY xx /*Takes any bag where contents of bag is equal to sum of items in bag and number of occurrences of item in bag. Had to avoid allowing machine to assign items that occur in neither.*/
            WHERE (xx:ELEMENTS+->NAT1)
                  & (dom(xx) = dom(bag)\/ran(ss))
                  & !(yy).(yy:ELEMENTS & yy:dom(bag)=>xx(yy)=bag(yy)+card(ss|>{yy}))
                  & !(yy).(yy:ELEMENTS & yy/:dom(bag) & yy:ran(ss)=>xx(yy)=card(ss|>{yy}))
                  & !(yy).(yy:ELEMENTS & yy/:dom(bag) & yy/:ran(ss)=>yy/:dom(xx))
           THEN
               bag:=xx
           END
    END;
    
    cc <-- totalcost = 
        cc:=SIGMA(xx).(xx:dom(bag)|bag(xx)*cost(xx))
END
