Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EL_TL_term_abbrevs.
Require Import ADD1_spec.
Require Import thm0_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1206053 (m : nat) (h1 : (S m) = (term0 m)) : (S m) = (term0 m).
Proof. exact (h1). Qed.
Lemma lem1206054 (m : nat) (h1 : (S m) = (term0 m)) : (term0 m) = (S m).
Proof. exact (SYM (@lem1206053 m h1)). Qed.
Lemma lem1206055 (m : nat) (h1 : (term0 m) = (S m)) : (term0 m) = (S m).
Proof. exact (h1). Qed.
Lemma lem1206056 (m : nat) (h1 : (term0 m) = (S m)) : (S m) = (term0 m).
Proof. exact (SYM (@lem1206055 m h1)). Qed.
Lemma lem1206057 (m : nat) : ((S m) = (term0 m)) = ((term0 m) = (S m)).
Proof. exact (prop_ext (fun h1 : (S m) = (term0 m) => @lem1206054 m h1) (fun h1 : (term0 m) = (S m) => @lem1206056 m h1)). Qed.
Lemma lem1206058 : term1 = term2.
Proof. exact (fun_ext (fun m : nat => @lem1206057 m)). Qed.
Lemma lem1206059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1206060 : term3 = term4.
Proof. exact (MK_COMB (@lem1206059) (@lem1206058)). Qed.
Lemma lem1206061 : term4.
Proof. exact (EQ_MP (@lem1206060) (@lem80621)). Qed.
Lemma lem1206064 (m : nat) : term5 m.
Proof. exact (@lem1206061 m). Qed.
Lemma lem1206065 (m : nat) : (term5 m) = ((term0 m) = (S m)).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem1206074 (m : nat) : (term0 m) = (S m).
Proof. exact (EQ_MP (@lem1206065 m) (@lem1206064 m)). Qed.
Lemma lem1206075 (n : nat) : (term0 n) = (S n).
Proof. exact (@lem1206074 n). Qed.
Lemma lem1206076 {_28223 : Type'} : (@EL _28223) = (@EL _28223).
Proof. exact (eq_refl (@EL _28223)). Qed.
Lemma lem1206077 {_28223 : Type'} (n : nat) : (term6 _28223 n) = (term7 _28223 n).
Proof. exact (MK_COMB (@lem1206076 _28223) (@lem1206075 n)). Qed.
Lemma lem1206078 {_28223 : Type'} (l : list _28223) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1206079 {_28223 : Type'} (n : nat) (l : list _28223) : (term8 _28223 n l) = (term9 _28223 n l).
Proof. exact (MK_COMB (@lem1206077 _28223 n) (@lem1206078 _28223 l)). Qed.
Lemma lem1206081 {_25569 : Type'} (n : nat) (l : list _25569) : (term9 _25569 n l) = (term10 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1206082 {_28223 : Type'} (n : nat) (l : list _28223) : (term9 _28223 n l) = (term10 _28223 n l).
Proof. exact (@lem1206081 _28223 n l). Qed.
Lemma lem1206083 {_28223 : Type'} (n : nat) (l : list _28223) : (term8 _28223 n l) = (term10 _28223 n l).
Proof. exact (TRANS (@lem1206079 _28223 n l) (@lem1206082 _28223 n l)). Qed.
Lemma lem1206084 {_28223 : Type'} (n : nat) (l : list _28223) : (term11 _28223 n l) = (term11 _28223 n l).
Proof. exact (eq_refl (term11 _28223 n l)). Qed.
Lemma lem1206085 {_28223 : Type'} (n : nat) (l : list _28223) : ((term10 _28223 n l) = (term8 _28223 n l)) = ((term10 _28223 n l) = (term10 _28223 n l)).
Proof. exact (MK_COMB (@lem1206084 _28223 n l) (@lem1206083 _28223 n l)). Qed.
Lemma lem1206087 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206088 {_28223 : Type'} (x : _28223) : (x = x) = True.
Proof. exact (@lem1206087 _28223 x). Qed.
Lemma lem1206089 {_28223 : Type'} (n : nat) (l : list _28223) : ((term10 _28223 n l) = (term10 _28223 n l)) = True.
Proof. exact (@lem1206088 _28223 (term10 _28223 n l)). Qed.
Lemma lem1206090 {_28223 : Type'} (n : nat) (l : list _28223) : ((term10 _28223 n l) = (term8 _28223 n l)) = True.
Proof. exact (TRANS (@lem1206085 _28223 n l) (@lem1206089 _28223 n l)). Qed.
Lemma lem1206091 {_28223 : Type'} (l : list _28223) : (term12 _28223 l) = term13.
Proof. exact (fun_ext (fun n : nat => @lem1206090 _28223 n l)). Qed.
Lemma lem1206092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1206093 {_28223 : Type'} (l : list _28223) : (term14 _28223 l) = term15.
Proof. exact (MK_COMB (@lem1206092) (@lem1206091 _28223 l)). Qed.
Lemma lem1206095 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206096 (t : Prop) : (term17 t) = t.
Proof. exact (@lem1206095 nat t). Qed.
Lemma lem1206097 : term15 = True.
Proof. exact (@lem1206096 True). Qed.
Lemma lem1206098 {_28223 : Type'} (l : list _28223) : (term14 _28223 l) = True.
Proof. exact (TRANS (@lem1206093 _28223 l) (@lem1206097)). Qed.
Lemma lem1206099 {_28223 : Type'} (l : list _28223) : True = (term14 _28223 l).
Proof. exact (SYM (@lem1206098 _28223 l)). Qed.
Lemma lem1206100 {_28223 : Type'} (l : list _28223) : term14 _28223 l.
Proof. exact (EQ_MP (@lem1206099 _28223 l) (@lem0)). Qed.
