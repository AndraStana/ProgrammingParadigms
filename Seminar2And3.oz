functor
import
System
Application
define

{ System.show '--------------------------'}

%............Seminar 3 - Pb 1......................
fun { Member Xs Y }
    case Xs 
    of nil then false
    [] H | T then 
                if  H == Y then true
                else { Member T Y}
                end
    end
end

X = [1 22 3 44]
Y = 32

{ System.show {Member X Y }}  

{ System.show '--------------------------'}



%............Seminar 3 - Pb 2......................

fun { Take Xs N }
    case Xs
    of nil then nil
    [] H|T then
            if N > 0 then H | { Take T N-1} 
            else nil
            end
    end
end


fun { Drop Xs N }
    case Xs
    of nil then nil
    [] H|T then
            if N > 0 then { Drop T N-1} 
            else Xs
            end
    end
end


X2 = [1 4 2 6 2]
Y2 = 3

{ System.show {Take X2 Y2 }}  

{ System.show '--------------------------'}

{ System.show {Drop X2 Y2 }}  

{ System.show '--------------------------'}


%............Seminar 3 - Pb 5......................

Expression = add(int(1) mul(int(3) int(4)))

fun { Eval Exp} 
    case Exp of int(Number) then Number
    [] add(Exp1 Exp2) then {Eval Exp1} + {Eval Exp2} 
    [] mul(Exp1 Exp2) then {Eval Exp1} * {Eval Exp2} 
    end
end

{System.show {Eval Expression }}


{ System.show '--------------------------'}



%............Seminar 2 - Pb 1......................



%...............a)..............

fun {Numerator InitialN N K}
    if N < InitialN - K + 1 then 1
    else N * {Numerator InitialN N-1 K}
    end
end

fun {Denominator K}
    if K==1 then 1
    else K * {Denominator K-1}
    end
end


fun {Comb1 N K}
    if K == 0 then 1
    else
        {Numerator N N K} div {Denominator K}
    end
end

{ System.show {Comb1 10 3}}


%...............b)..............



fun {Comb2Recursive N K Inc }
    if K == 0 then {Int.toFloat 1}
    else 
        if Inc == K
            then {Int.toFloat (N-K+1) } / {Int.toFloat K}
        else
            (  {Int.toFloat (N - Inc + 1)} / {Int.toFloat Inc} ) * { Comb2Recursive N K (Inc + 1)}
        end
    end
end

fun {Comb2 N K}
    {Comb2Recursive N K 1}
end









{Application.exit 0}
end