functor
import
System
Application
define



%............Seminar 3 - Pb 1......................
{ System.show '--------------------------'}


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




%............Seminar 3 - Pb 2......................
{ System.show '--------------------------'}


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





%............Seminar 2 - Pb 1......................
{ System.show '--------------------------'}



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

{ System.show {Comb2 10 3}}


%............Seminar 2 - Pb 4......................
{ System.show '--------------------------'}


fun {IsLeaf Node}
    if Node == nil then false
    else
        if {And Node.2==nil Node.3==nil} then true
        else false
        end
    end
end


fun {Insert Tree Value}
        if {IsLeaf Tree} then 
            if Value < Tree.1 then
                node( Tree.1 node(Value nil nil) nil )
            else
                node( Tree.1 nil node(Value nil nil) ) 
            end
        else
            local LeftTree RightTree ReturnedTree in

                if Value < Tree.1 then
                    if Tree.2 \= nil 
                        then LeftTree = {Insert Tree.2 Value }
                    else LeftTree= nil
                    end
                else
                    LeftTree = Tree.2
                end

                if Value >= Tree.1 then
                    if Tree.3 \= nil 
                        then RightTree = {Insert Tree.3 Value }
                    else RightTree = nil
                    end
                else
                    RightTree = Tree.3
                end

                ReturnedTree = node(Tree.1 LeftTree RightTree )

                ReturnedTree
            end
    end
end


fun {Smallest Tree}

    if Tree.2 \= nil then 
        {Smallest Tree.2}
    else
        Tree.1
    end
end

fun {Biggest Tree}

    if Tree.3 \= nil then 
        {Biggest Tree.3}
    else
        Tree.1
    end
end


fun {IsSortedBST Tree}
    if Tree == nil then true
    else
        local IsBiggest IsSmallest in 

            if Tree.2 == nil then IsBiggest = true
            else IsBiggest = {Biggest Tree.2} < Tree.1
            end

            if Tree.3 == nil then IsSmallest = true
            else IsSmallest = {Smallest Tree.3} >= Tree.1
            end

            if  {And IsBiggest IsSmallest}
            then 
                {And {IsSortedBST Tree.2} {IsSortedBST Tree.3}}
            else
                false
            end

        end

    end
end

%-----------------TEST TREE--------------------


P1 = node(8 P2 P7)
    P2 = node(3 P3 P4)
        P3 = node(1 nil nil)
        P4 = node(6 P5 P6)
            P5 = node(5 nil nil)
            P6 = node(7 nil nil)

    P7 = node(11 P8 P9)
        P8 = node(10 nil nil)
        P9 = node(14 nil nil)


{ System.show '+++++++++++++  INSERTION +++++++++++++++++++++'}

{System.show {Insert P1 2}}
{ System.show '--------'}
{System.show {Insert P1 9}}
{ System.show '--------'}
{System.show {Insert P1 8}}

{ System.show '+++++++++++++++ SMALLEST/ BIGGEST  +++++++++++++++++++'}
{System.show {Smallest P1}}
{System.show {Biggest P1}}

{ System.show '+++++++++++++++ IS SORTED  +++++++++++++++++++'}
{System.show {IsSortedBST P1}}




%............Seminar 4 - Pb 2......................
{ System.show '--------------------------'}

fun {IsMember Env Id}
    case Env
    of nil then false
    [] H | T then 
        case H of (IdH#ExpH) then
            
            if IdH == Id then true
            else {IsMember T Id}
            end
        
        end
    end
end
     
EnvL = [ a#abb b#bcc c#cdd ]
{System.show {IsMember EnvL c}}



fun {Fetch Env Id}
    case Env
    of nil then Id
    [] H | T then 
        case H of (IdH#ExpH) then
            
            if IdH == Id then ExpH
            else {Fetch T Id}
            end
        
        end
    end
end

{System.show {Fetch EnvL a}}



fun {AdJoin Env IdExp}
    case Env
    of nil then [IdExp]
    [] H | T then 
        case H of (IdH#ExpH) then
            
            case IdExp of (NewId#NewExp) then

                if IdH == NewId then IdExp | T
                else  H | {AdJoin T IdExp}
                end

            end
        
        end
    end
end

{System.show {AdJoin EnvL c#sss}}


% fun {Ceva Ee} 
%     if true then true else false end
% end


% {System.show {Ceva apply(let(x#y) y ) }   }

% XXXX = apply(let(x#y) y)





{Application.exit 0}
end






