Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8048831 : forall {_142753 _142754 _142755 : Type'}, forall f : ((cart _142753 _142754) -> Prop) -> Prop, forall g : ((cart _142753 _142755) -> Prop) -> Prop, (@PCROSS _142753 _142754 _142755 (@UNIONS (cart _142753 _142754) f) (@UNIONS (cart _142753 _142755) g)) = (@UNIONS (cart _142753 (finite_sum _142754 _142755)) (@GSPEC ((cart _142753 (finite_sum _142754 _142755)) -> Prop) (fun GEN_PVAR_362 : (cart _142753 (finite_sum _142754 _142755)) -> Prop => exists s : (cart _142753 _142754) -> Prop, exists t : (cart _142753 _142755) -> Prop, @SETSPEC ((cart _142753 (finite_sum _142754 _142755)) -> Prop) GEN_PVAR_362 ((@IN ((cart _142753 _142754) -> Prop) s f) /\ (@IN ((cart _142753 _142755) -> Prop) t g)) (@PCROSS _142753 _142754 _142755 s t)))).
