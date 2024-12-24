Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_AC_term_abbrevs.
Require Import INSERT_COMM_spec.
Require Import INSERT_INSERT_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3291086 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3277193 A x). Qed.
Lemma lem3291087 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3291088 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3291087 A x) (@lem3291086 A x)). Qed.
Lemma lem3291089 {A : Type'} (x : A) (s : A -> Prop) : term2 A x s.
Proof. exact (@lem3291088 A x s). Qed.
Lemma lem3291090 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = ((term3 A x s) = (@INSERT A x s)).
Proof. exact (eq_refl (term2 A x s)). Qed.
Lemma lem3291092 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3278336 A x). Qed.
Lemma lem3291093 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem3291094 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem3291093 A x) (@lem3291092 A x)). Qed.
Lemma lem3291095 {A : Type'} (x : A) (y : A) : term6 A x y.
Proof. exact (@lem3291094 A x y). Qed.
Lemma lem3291096 {A : Type'} (y : A) (x : A) : (term6 A x y) = (term7 A y x).
Proof. exact (eq_refl (term6 A x y)). Qed.
Lemma lem3291097 {A : Type'} (y : A) (x : A) : term7 A y x.
Proof. exact (EQ_MP (@lem3291096 A y x) (@lem3291095 A x y)). Qed.
Lemma lem3291098 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term8 A y x s.
Proof. exact (@lem3291097 A y x s). Qed.
Lemma lem3291099 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A y x s) = ((term9 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term8 A y x s)). Qed.
Lemma lem3291113 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term9 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3291099 A y x s) (@lem3291098 A y x s)). Qed.
Lemma lem3291114 {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop) : (term9 _86293 x y s) = (term9 _86293 y x s).
Proof. exact (@lem3291113 _86293 y x s). Qed.
Lemma lem3291115 {_86293 : Type'} (x : _86293) (y : _86293) (s : _86293 -> Prop) : (term9 _86293 y x s) = (term9 _86293 x y s).
Proof. exact (@lem3291114 _86293 x y s). Qed.
Lemma lem3291121 {_86293 : Type'} (x : _86293) (y : _86293) (s : _86293 -> Prop) : (term10 _86293 x y s) = (term10 _86293 x y s).
Proof. exact (eq_refl (term10 _86293 x y s)). Qed.
Lemma lem3291122 {_86293 : Type'} (x : _86293) (y : _86293) (s : _86293 -> Prop) : ((term9 _86293 x y s) = (term9 _86293 y x s)) = ((term9 _86293 x y s) = (term9 _86293 x y s)).
Proof. exact (MK_COMB (@lem3291121 _86293 x y s) (@lem3291115 _86293 x y s)). Qed.
Lemma lem3291124 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3291125 {_86293 : Type'} (x : _86293 -> Prop) : (x = x) = True.
Proof. exact (@lem3291124 (_86293 -> Prop) x). Qed.
Lemma lem3291126 {_86293 : Type'} (x : _86293) (y : _86293) (s : _86293 -> Prop) : ((term9 _86293 x y s) = (term9 _86293 x y s)) = True.
Proof. exact (@lem3291125 _86293 (term9 _86293 x y s)). Qed.
Lemma lem3291127 {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop) : ((term9 _86293 x y s) = (term9 _86293 y x s)) = True.
Proof. exact (TRANS (@lem3291122 _86293 x y s) (@lem3291126 _86293 x y s)). Qed.
Lemma lem3291128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3291129 {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop) : (term11 _86293 y x s) = (and True).
Proof. exact (MK_COMB (@lem3291128) (@lem3291127 _86293 y x s)). Qed.
Lemma lem3291133 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (@INSERT A x s).
Proof. exact (EQ_MP (@lem3291090 A x s) (@lem3291089 A x s)). Qed.
Lemma lem3291134 {_86293 : Type'} (x : _86293) (s : _86293 -> Prop) : (term3 _86293 x s) = (@INSERT _86293 x s).
Proof. exact (@lem3291133 _86293 x s). Qed.
Lemma lem3291135 {_86293 : Type'} : (@eq (_86293 -> Prop)) = (@eq (_86293 -> Prop)).
Proof. exact (eq_refl (@eq (_86293 -> Prop))). Qed.
Lemma lem3291136 {_86293 : Type'} (x : _86293) (s : _86293 -> Prop) : (term12 _86293 x s) = (term13 _86293 x s).
Proof. exact (MK_COMB (@lem3291135 _86293) (@lem3291134 _86293 x s)). Qed.
Lemma lem3291137 {_86293 : Type'} (x : _86293) (s : _86293 -> Prop) : (@INSERT _86293 x s) = (@INSERT _86293 x s).
Proof. exact (eq_refl (@INSERT _86293 x s)). Qed.
Lemma lem3291138 {_86293 : Type'} (x : _86293) (s : _86293 -> Prop) : ((term3 _86293 x s) = (@INSERT _86293 x s)) = ((@INSERT _86293 x s) = (@INSERT _86293 x s)).
Proof. exact (MK_COMB (@lem3291136 _86293 x s) (@lem3291137 _86293 x s)). Qed.
Lemma lem3291140 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3291141 {_86293 : Type'} (x : _86293 -> Prop) : (x = x) = True.
Proof. exact (@lem3291140 (_86293 -> Prop) x). Qed.
Lemma lem3291142 {_86293 : Type'} (x : _86293) (s : _86293 -> Prop) : ((@INSERT _86293 x s) = (@INSERT _86293 x s)) = True.
Proof. exact (@lem3291141 _86293 (@INSERT _86293 x s)). Qed.
Lemma lem3291143 {_86293 : Type'} (x : _86293) (s : _86293 -> Prop) : ((term3 _86293 x s) = (@INSERT _86293 x s)) = True.
Proof. exact (TRANS (@lem3291138 _86293 x s) (@lem3291142 _86293 x s)). Qed.
Lemma lem3291144 {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop) : (term14 _86293 y x s) = (True /\ True).
Proof. exact (MK_COMB (@lem3291129 _86293 y x s) (@lem3291143 _86293 x s)). Qed.
Lemma lem3291146 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3291147 : (True /\ True) = True.
Proof. exact (@lem3291146 True). Qed.
Lemma lem3291148 {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop) : (term14 _86293 y x s) = True.
Proof. exact (TRANS (@lem3291144 _86293 y x s) (@lem3291147)). Qed.
Lemma lem3291149 {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop) : True = (term14 _86293 y x s).
Proof. exact (SYM (@lem3291148 _86293 y x s)). Qed.
Lemma lem3291150 {_86293 : Type'} (y : _86293) (x : _86293) (s : _86293 -> Prop) : term14 _86293 y x s.
Proof. exact (EQ_MP (@lem3291149 _86293 y x s) (@lem0)). Qed.
