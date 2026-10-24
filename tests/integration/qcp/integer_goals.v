(* QCP-V2.1.4 generated condition excerpts; see provenance.json and LICENSE. *)

Definition gcd_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (y_pre <> 0)) (PreH2 : (x_pre <= INT_MAX)) (PreH3 : (y_pre <= INT_MAX)) (PreH4 : (y_pre >= INT_MIN)) (PreH5 : (INT_MIN < x_pre)) (PreH6 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ ((x_pre <> (INT_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition gcd_entail_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (x_pre <= INT_MAX) ” 
  &&  “ (y_pre <= INT_MAX) ” 
  &&  “ (y_pre >= INT_MIN) ” 
  &&  “ (INT_MIN < x_pre) ” 
  &&  “ (INT_MIN < y_pre) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
.

Definition gcd_partial_solve_wit_2_pure_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (PreH1 : (x_pre >= INT_MIN)) (PreH2 : (y_pre <> 0)) (PreH3 : (x_pre <= INT_MAX)) (PreH4 : (y_pre <= INT_MAX)) (PreH5 : (y_pre >= INT_MIN)) (PreH6 : (INT_MIN < x_pre)) (PreH7 : (INT_MIN < y_pre)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
|--
  “ (INT_MIN < (x_pre % ( y_pre ) )) ”
.

Definition Always_positive_simple_safety_wit_4 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |->_)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
|--
  “ ((b_pre * b_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (b_pre * b_pre )) ”
.

Definition Always_positive_simple_safety_wit_6 := 
forall (c_pre: Z) (b_pre: Z) (a_pre: Z) (PreH1 : (a_pre <> 0)) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) (PreH6 : (INT_MIN < c_pre)) (PreH7 : (c_pre <= INT_MAX)) ,
  ((( &( "delta2" ) )) # Int64  |->_)
  **  ((( &( "delta1" ) )) # Int64  |-> ((b_pre * b_pre ) ÷ 4 ))
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "c" ) )) # Int  |-> c_pre)
|--
  “ ((a_pre * c_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (a_pre * c_pre )) ”
.
