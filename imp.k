module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax AExp  ::= Int | Id
                 | "++" Id
                 | "read" "(" ")"
                 // remove division tag when we have proper search strategies
                 | "-" Int
                 > AExp "/" AExp              [left, strict, division]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool | Id
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | AExp ">=" AExp             [strict]    
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | Id "=" BExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | AExp "=" BExp "?" AExp ":" AExp ";"
                 | "do" Block
                   "while" "(" BExp ")" ";"   
                 | "int(" BExp ")"";"
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "print" "(" Int ")" ";"
                 | "halt" ";"
                 > "spawn" Stmt
                 > Stmt Stmt                  [left]

  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  // K does not yet handle automatically subsorting one user defined list to
  // another when the elements are subsorted, so we must do it manually.
  syntax AExps ::= Ids
endmodule


module IMP
  imports IMP-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Stmt </k>
                  <state color="red"> .Map </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I => 0 -Int I
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule _ if (B)  S1 else S2 => if (B)  S1 else S2 ~> B
  rule while (B) S => if (B) {S while (B) S} else {}[structural]
 
  rule int(B); => B
  rule <k> X = (true) ? I:Int : E:Int; => . ...</k> <state>... X |->(_ => I) ...</state>
  rule <k> X = (false) ? I:Int : E:Int; => . ...</k> <state>... X |->(_ => E) ...</state>
  rule do B1:Block while (B2); => if (B2) { do B1 while (B2); } else {} ~> B1 [structural] 

  rule print(I:Int); => I

  rule <k> int (X,Xs => Xs); ...</k>
       <state> Rho (.Map => X |-> 0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; => .  [structural]
endmodule
