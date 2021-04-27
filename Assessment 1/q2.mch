/* q2
* Author: u1604303

* Creation date: 31/10/2019

*/

MACHINE
    
    q2
    
SETS
    
    ITEMS = {ww, tt}
    
CONSTANTS
    
    backloglim
    
PROPERTIES
    
    backloglim:NAT1 &
    
    backloglim = 500
    
VARIABLES
    
    orders, stock
    
INVARIANT
    
    orders: seq(ITEMS +-> NAT1) &
    
    !(xx).(xx:ran(orders) => dom(xx) /= {}) &
    
    size(orders) <= backloglim &
    
    stock: ITEMS --> NAT
    
INITIALISATION
    
    orders := [] ||
    
    stock := {xx,yy | xx:ITEMS & yy=0}
    
OPERATIONS
    
    recieveorder(oo) =
    
    PRE
        
        oo: ITEMS +-> NAT1 &
        
        dom(oo) /= {} &
        
        size(orders) < backloglim
        
    THEN
        
        orders := orders <- oo
        
    END;
    
    
    recievestock(ss) =
    
    PRE
        
        ss: ITEMS +-> NAT1 &
        
        dom(ss) /= {}
        
    THEN
        
        stock := stock <+ {ii,nn | ii:dom(ss) & nn=(stock(ii) + ss(ii))}
        
    END;
    
    
    aa <-- howmany(ii) =
    
    PRE
        
        ii:ITEMS
        
    THEN
        
        aa := stock(ii)
        
    END;
    
    
    aa <-- whereisitem(ii) =
    
    PRE
        
        ii:ITEMS
        
    THEN
        
        aa := {oo | oo:ran(orders) & ii:dom(oo)}
        
    END;
    
    
    aa <-- totordered(ii) =
    
    PRE
        
        ii:ITEMS
        
    THEN
        
        aa := SIGMA(nn).(nn:1..size(orders) & ii:dom(orders(nn)) | orders(nn)(ii))
        
    END;
    
    
    aa <-- lowstock(nn) =
    
    PRE
        
        nn:NAT
        
    THEN
        
        aa := {ii | ii:ITEMS & stock(ii) < nn}
        
    END;
    
    
    aa <-- oneoflowest =
    
    PRE
        
        aa:ITEMS
        
    THEN
        
        ANY
            
            xx
            
        WHERE
            
            xx:ITEMS &
            
            !(yy).(yy:ITEMS => stock(xx) <= stock(yy))
            
        THEN
            
            aa := xx
            
        END
        
    END;
    
    
    serviceorder =
    
    PRE
        
        orders /= []
        
    THEN
        
        IF
            
            !(yy).(yy:dom(orders(1)) => orders(1)(yy) <= stock(yy))
            
        THEN
            
            stock := stock <+ {ii,nn | ii:dom(orders(1)) & nn=(stock(ii) - orders(1)(ii))} ||
            
            orders := orders \|/ 1
            
        END
        
    END;
    
    
    complicatedserviceorder =
    
    PRE
        
        orders /= []
        
    THEN
        
        ANY
            
            xx
            
        WHERE
            
            xx = {nn | nn:1..size(orders) & !(zz).(zz:(dom(orders(nn))) => orders(nn)(zz) <= stock(zz)) }
            
        THEN
            
            IF
                
                xx /= {}
                
            THEN
                
                stock := stock <+ {ii,nn | ii:dom(orders(min(xx))) & nn=stock(ii) - orders(min(xx))(ii)} ||
                
                orders := (orders /|\ min(xx) - 1) ^ (orders \|/ min(xx))
                
            END
            
        END
        
    END
    
END