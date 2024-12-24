Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_0_term_abbrevs.
Require Import thm0_spec.
Require Import thm135075_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm76885_spec.
Lemma lem135086 : term0.
Proof. exact (proj1 (@lem135075)). Qed.
Lemma lem135087 (m : nat) : term1 m.
Proof. exact (@lem135086 m). Qed.
Lemma lem135088 (m : nat) : (term1 m) = ((term2 m) = m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem135101 (m : nat) : (term2 m) = m.
Proof. exact (EQ_MP (@lem135088 m) (@lem135087 m)). Qed.
Lemma lem135102 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135103 (m : nat) : (term3 m) = (@eq nat m).
Proof. exact (MK_COMB (@lem135102) (@lem135101 m)). Qed.
Lemma lem135104 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem135105 (m : nat) : ((term2 m) = m) = (m = m).
Proof. exact (MK_COMB (@lem135103 m) (@lem135104 m)). Qed.
Lemma lem135107 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135108 (x : nat) : (x = x) = True.
Proof. exact (@lem135107 nat x). Qed.
Lemma lem135109 (m : nat) : (m = m) = True.
Proof. exact (@lem135108 m). Qed.
Lemma lem135110 (m : nat) : ((term2 m) = m) = True.
Proof. exact (TRANS (@lem135105 m) (@lem135109 m)). Qed.
Lemma lem135111 (m : nat) : (term4 m) = (term4 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem135112 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem135111 m) (@lem135110 m)). Qed.
Lemma lem135114 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem135115 (m : nat) : (term6 m) = ((term7 m) = (NUMERAL 0)).
Proof. exact (@lem135114 ((term7 m) = (NUMERAL 0))). Qed.
Lemma lem135118 (m : nat) : (term5 m) = ((term7 m) = (NUMERAL 0)).
Proof. exact (TRANS (@lem135112 m) (@lem135115 m)). Qed.
Lemma lem135119 : term8 = term9.
Proof. exact (fun_ext (fun m : nat => @lem135118 m)). Qed.
Lemma lem135120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135121 : term10 = term11.
Proof. exact (MK_COMB (@lem135120) (@lem135119)). Qed.
Lemma lem135126 : term11 = term10.
Proof. exact (SYM (@lem135121)). Qed.
Lemma lem135128 (P : nat -> Prop) : term12 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135129 : term13.
Proof. exact (@lem135128 term9). Qed.
Lemma lem135130 : term14 = (term15 = (NUMERAL 0)).
Proof. exact (eq_refl term14). Qed.
Lemma lem135131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135132 : term16 = term17.
Proof. exact (MK_COMB (@lem135131) (@lem135130)). Qed.
Lemma lem135133 (m : nat) : (term18 m) = ((term7 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem135134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135135 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem135134) (@lem135133 m)). Qed.
Lemma lem135136 (m : nat) : (term21 m) = ((term22 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem135137 (m : nat) : (term23 m) = (term24 m).
Proof. exact (MK_COMB (@lem135135 m) (@lem135136 m)). Qed.
Lemma lem135138 : term25 = term26.
Proof. exact (fun_ext (fun m : nat => @lem135137 m)). Qed.
Lemma lem135139 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135140 : term27 = term28.
Proof. exact (MK_COMB (@lem135139) (@lem135138)). Qed.
Lemma lem135141 : term29 = term30.
Proof. exact (MK_COMB (@lem135132) (@lem135140)). Qed.
Lemma lem135142 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135143 : term31 = term32.
Proof. exact (MK_COMB (@lem135142) (@lem135141)). Qed.
Lemma lem135144 (m : nat) : (term18 m) = ((term7 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem135145 : term33 = term9.
Proof. exact (fun_ext (fun m : nat => @lem135144 m)). Qed.
Lemma lem135146 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135147 : term34 = term11.
Proof. exact (MK_COMB (@lem135146) (@lem135145)). Qed.
Lemma lem135148 : term13 = term35.
Proof. exact (MK_COMB (@lem135143) (@lem135147)). Qed.
Lemma lem135149 : term35.
Proof. exact (EQ_MP (@lem135148) (@lem135129)). Qed.
Lemma lem135163 : term0.
Proof. exact (proj1 (@lem135075)). Qed.
Lemma lem135164 (m : nat) : term1 m.
Proof. exact (@lem135163 m). Qed.
Lemma lem135165 (m : nat) : (term1 m) = ((term2 m) = m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem135170 (m : nat) : (term2 m) = m.
Proof. exact (EQ_MP (@lem135165 m) (@lem135164 m)). Qed.
Lemma lem135171 : term15 = (NUMERAL 0).
Proof. exact (@lem135170 (NUMERAL 0)). Qed.
Lemma lem135172 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135173 : term36 = term37.
Proof. exact (MK_COMB (@lem135172) (@lem135171)). Qed.
Lemma lem135174 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem135175 : (term15 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem135173) (@lem135174)). Qed.
Lemma lem135177 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135178 (x : nat) : (x = x) = True.
Proof. exact (@lem135177 nat x). Qed.
Lemma lem135179 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem135178 (NUMERAL 0)). Qed.
Lemma lem135180 : (term15 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem135175) (@lem135179)). Qed.
Lemma lem135181 : True = (term15 = (NUMERAL 0)).
Proof. exact (SYM (@lem135180)). Qed.
Lemma lem135182 : term15 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem135181) (@lem0)). Qed.
Lemma lem135188 : term38.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem135189 (m : nat) : term39 m.
Proof. exact (@lem135188 m). Qed.
Lemma lem135190 (m : nat) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem135191 (m : nat) : term40 m.
Proof. exact (EQ_MP (@lem135190 m) (@lem135189 m)). Qed.
Lemma lem135192 (m : nat) (n : nat) : term41 m n.
Proof. exact (@lem135191 m n). Qed.
Lemma lem135193 (m : nat) (n : nat) : (term41 m n) = ((term42 m n) = (term43 m n)).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem135202 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (EQ_MP (@lem135193 m n) (@lem135192 m n)). Qed.
Lemma lem135203 (m : nat) : (term22 m) = (term44 m).
Proof. exact (@lem135202 (NUMERAL 0) m). Qed.
Lemma lem135205 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : (term7 m) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem135206 : Nat.pred = Nat.pred.
Proof. exact (eq_refl Nat.pred). Qed.
Lemma lem135207 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : (term44 m) = term45.
Proof. exact (MK_COMB (@lem135206) (@lem135205 m h1)). Qed.
Lemma lem135209 : term45 = (NUMERAL 0).
Proof. exact (proj1 (@lem76885)). Qed.
Lemma lem135210 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : (term44 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem135207 m h1) (@lem135209)). Qed.
Lemma lem135211 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : (term22 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem135203 m) (@lem135210 m h1)). Qed.
Lemma lem135212 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135213 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : (term46 m) = term37.
Proof. exact (MK_COMB (@lem135212) (@lem135211 m h1)). Qed.
Lemma lem135214 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem135215 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : ((term22 m) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem135213 m h1) (@lem135214)). Qed.
Lemma lem135217 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135218 (x : nat) : (x = x) = True.
Proof. exact (@lem135217 nat x). Qed.
Lemma lem135219 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem135218 (NUMERAL 0)). Qed.
Lemma lem135220 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : ((term22 m) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem135215 m h1) (@lem135219)). Qed.
Lemma lem135221 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : True = ((term22 m) = (NUMERAL 0)).
Proof. exact (SYM (@lem135220 m h1)). Qed.
Lemma lem135222 (m : nat) (h1 : (term7 m) = (NUMERAL 0)) : (term22 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem135221 m h1) (@lem0)). Qed.
Lemma lem135223 (m : nat) : term24 m.
Proof. exact (fun h0 : (term7 m) = (NUMERAL 0) => @lem135222 m h0). Qed.
Lemma lem135228 : term28.
Proof. exact (fun m : nat => @lem135223 m). Qed.
Lemma lem135229 : term30.
Proof. exact (conj (@lem135182) (@lem135228)). Qed.
Lemma lem135230 : term11.
Proof. exact (@lem135149 (@lem135229)). Qed.
Lemma lem135231 : term10.
Proof. exact (EQ_MP (@lem135126) (@lem135230)). Qed.
