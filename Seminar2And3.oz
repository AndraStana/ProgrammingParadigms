functor
import
System
Application
define


%............Seminar 1 - Pb 1......................

fun { Abs Y}
   if { Int.is Y} then
      if Y<0 then Y*(~1)
      else Y
      end
   else
      if { Float.is Y} then
	 if Y<0.0 then Y*(~1.0)
	    else Y end
	 else 0 end
   end
end

 { System.show '-------S1P1-----Abs tests: '}
 { System.show {Abs ~2}}
 { System.show {Abs 4}}
 { System.show {Abs  5.2}}
 { System.show {Abs  ~3.5}}

 %............Seminar 1 - Pb 2......................
%Pb2 power: n^m, n-integer, m-natural
fun {Pow N M}
   if M==0 then 1
   else
      {Pow N M-1} * N
   end
end

{ System.show '-------S1P2-----Pow tests: '}
{ System.show {Pow 2 3}}
{ System.show {Pow 0 10}}
{ System.show {Pow 4 0}}
{ System.show {Pow ~2 3}}
{ System.show {Pow ~3 0}}
{ System.show {Pow ~4 1}}

 %............Seminar 1 - Pb 3......................
%Pb3 - max recursively: max of 2 natural numbers; allowed to test only if a number is 0 !!
% n>=0, m>=0
fun {MaxRec N M}
   if N==0 then M
   else
      if M==0 then N
      else
	 1+ {MaxRec N-1 M-1}
      end
   end
end
{ System.show '-------S1P3-----Maximum Recursive tests: '}
{ System.show {MaxRec 0 0}}
{ System.show {MaxRec 4 4}}
{ System.show {MaxRec 40 55}}
{ System.show {MaxRec 23 18}}

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

%............Seminar 2 - Pb 2......................
%Seminar 2, pb2 - Simplified version of the reverse algorithm
fun { Reverse L1 L2 }
   case L1 of
      nil then L2
      [] H | T then { Reverse T H|L2 }  
   end
end

{ System.show '-------S2P2-----Reverse tests: '}

X3 = [a b c]
Y3 = nil
{ System.show { Reverse X3 Y3}}


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



%............Seminar 4 - Pb 1......................
{ System.show '--------------------------'}


fun {CombineLists L1 L2}
    case L1
    of nil then L2
    [] H | T then {CombineLists T H | L2 }
    end
end


fun {GetFreeRecursive Exp Bounds}
    case Exp of
    
    apply(Exp1 Exp2) then
         {CombineLists {GetFreeRecursive Exp1 Bounds} {GetFreeRecursive Exp2 Bounds} }

    [] lam(Id Exp1) then
        {GetFreeRecursive Exp1 Id | Bounds }

    [] let(Id#Exp1 Exp2 ) then
        {CombineLists {GetFreeRecursive Exp1 Id | Bounds} {GetFreeRecursive Exp2 Id | Bounds} }

    [] Id then
        if {Member Bounds Id} then nil
        else [ Id ]
        end

    end
end




fun {FreeSet Exp}
    {GetFreeRecursive Exp nil}
end




Incerc1 = aaa
Incerc2 = lam(aaa aaa)
Incerc3 = let(aaa#z aaa)
Incerc4 = lam(x apply(y x))
Incerc5 = apply(x let(x#y x))
Incerc6 = apply(y apply(let(x#x x) y))



{System.show {FreeSet Incerc1} }
{System.show {FreeSet Incerc2} }
{System.show {FreeSet Incerc3} }
{System.show {FreeSet Incerc4} }
{System.show {FreeSet Incerc5} }
{System.show {FreeSet Incerc6} }

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






%............Seminar 4 - Pb 3......................
{System.show '............................. RENAAAAAAAAAAAMEEE .................'}



Cnt = {NewCell 0}
fun {NewId}
    Cnt :=  @Cnt + 1
    { String.toAtom { Append "id<" {Append { Int.toString @Cnt} ">"  }}}
end


fun {DeleteFromList List Elem}
    case List of 
        nil then nil
        [] H | T then
            if H == Elem then  {DeleteFromList T Elem}
            else H | {DeleteFromList T Elem}
            end
    end
end


fun {RenameRec Exp Env FreeVars }
    case Exp of 

    lam(Exp1 Exp2) then 
        lam( {RenameRec Exp1 Env FreeVars} {RenameRec Exp2 Env FreeVars}  )
        
    [] let(Id#Exp1 Exp2) then 
        local NewName in
            NewName = {NewId}
            Env := {AdJoin @Env Id#NewName}
            
            let( NewName#{RenameRec Exp1 Env {DeleteFromList FreeVars Id}} {RenameRec Exp2 Env {DeleteFromList FreeVars Id}}  )
        end
    
    [] apply(Exp1 Exp2) then 
       

        apply( {RenameRec Exp1 Env FreeVars} {RenameRec Exp2 Env FreeVars}  )

    [] Id then

        if {Member FreeVars Id} then Id
        else
            if {IsMember @Env Id} then {Fetch @Env Id}

            else
                local NewName in
                    NewName = {NewId}
                    Env := {AdJoin @Env Id#NewName}
                    NewName
                end
            end
        end
    end
end


fun {Rename Exp }
    local FreeVars = {FreeSet Exp}  LocalEnv = {NewCell nil} Response in
        Response = {RenameRec Exp LocalEnv FreeVars}
        Response
    end
    
end



Test1 = lam(aaa aaa)
{System.show {Rename Test1}}

Test2 = let(aaa#z aaa)
{System.show {Rename Test2}}


Test3 = lam(z lam(x z))
{System.show {Rename Test3}}

Test4 = let(id#lam(z z) apply(id y))
{System.show {Rename Test4}}



{Application.exit 0}
end






