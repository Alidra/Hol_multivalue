Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1052197_term_abbrevs.
Require Import INJ_INVERSE2_spec.
Require Import NUMPAIR_INJ_spec.
Require Import SKOLEM_THM_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1052147 {A B C : Type'} (P : type1412 A B C) : term0 A B C P.
Proof. exact (@lem1046586 A B C P). Qed.
Lemma lem1052148 {A B C : Type'} (P : type1412 A B C) : (term0 A B C P) = (term1 A B C P).
Proof. exact (eq_refl (term0 A B C P)). Qed.
Lemma lem1052151 {A B C : Type'} (P : type1412 A B C) : term1 A B C P.
Proof. exact (EQ_MP (@lem1052148 A B C P) (@lem1052147 A B C P)). Qed.
Lemma lem1052152 (P : type1606) : term2 P.
Proof. exact (@lem1052151 nat nat nat P). Qed.
Lemma lem1052153 : term3.
Proof. exact (@lem1052152 NUMPAIR). Qed.
Lemma lem1052154 : term4.
Proof. exact (@lem1052153 (@lem1052146)). Qed.
Lemma lem1052155 : term5.
Proof. exact (fun _17340 : type1671 => @lem1052154). Qed.
Lemma lem1052156 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1052157 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term7 A B P) = (term8 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem1052160 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem1052157 A B P) (@lem1052156 A B P)). Qed.
Lemma lem1052161 (P : type1269) : (term9 P) = (term10 P).
Proof. exact (@lem1052160 type1671 (nat -> nat) P). Qed.
Lemma lem1052162 : term11 = term12.
Proof. exact (@lem1052161 term13). Qed.
Lemma lem1052163 (_17340 : type1671) : (term14 _17340) = term15.
Proof. exact (eq_refl (term14 _17340)). Qed.
Lemma lem1052164 (X : nat -> nat) : X = X.
Proof. exact (eq_refl X). Qed.
Lemma lem1052165 (_17340 : type1671) (X : nat -> nat) : (term16 _17340 X) = (term17 X).
Proof. exact (MK_COMB (@lem1052163 _17340) (@lem1052164 X)). Qed.
Lemma lem1052166 (X : nat -> nat) : (term17 X) = (term18 X).
Proof. exact (eq_refl (term17 X)). Qed.
Lemma lem1052167 (_17340 : type1671) (X : nat -> nat) : (term16 _17340 X) = (term18 X).
Proof. exact (TRANS (@lem1052165 _17340 X) (@lem1052166 X)). Qed.
Lemma lem1052168 (_17340 : type1671) : (term19 _17340) = term15.
Proof. exact (fun_ext (fun X : nat -> nat => @lem1052167 _17340 X)). Qed.
Lemma lem1052169 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1052170 (_17340 : type1671) : (term20 _17340) = term4.
Proof. exact (MK_COMB (@lem1052169) (@lem1052168 _17340)). Qed.
Lemma lem1052171 : term21 = term22.
Proof. exact (fun_ext (fun _17340 : type1671 => @lem1052170 _17340)). Qed.
Lemma lem1052172 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1052173 : term11 = term5.
Proof. exact (MK_COMB (@lem1052172) (@lem1052171)). Qed.
Lemma lem1052174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1052175 : term23 = term24.
Proof. exact (MK_COMB (@lem1052174) (@lem1052173)). Qed.
Lemma lem1052176 (_17340 : type1671) : (term14 _17340) = term15.
Proof. exact (eq_refl (term14 _17340)). Qed.
Lemma lem1052177 (X : type1272) (_17340 : type1671) : (X _17340) = (X _17340).
Proof. exact (eq_refl (X _17340)). Qed.
Lemma lem1052178 (X : type1272) (_17340 : type1671) : (term25 X _17340) = (term26 X _17340).
Proof. exact (MK_COMB (@lem1052176 _17340) (@lem1052177 X _17340)). Qed.
Lemma lem1052179 (X : type1272) (_17340 : type1671) : (term26 X _17340) = (term27 X _17340).
Proof. exact (eq_refl (term26 X _17340)). Qed.
Lemma lem1052180 (X : type1272) (_17340 : type1671) : (term25 X _17340) = (term27 X _17340).
Proof. exact (TRANS (@lem1052178 X _17340) (@lem1052179 X _17340)). Qed.
Lemma lem1052181 (X : type1272) : (term28 X) = (term29 X).
Proof. exact (fun_ext (fun _17340 : type1671 => @lem1052180 X _17340)). Qed.
Lemma lem1052182 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1052183 (X : type1272) : (term30 X) = (term31 X).
Proof. exact (MK_COMB (@lem1052182) (@lem1052181 X)). Qed.
Lemma lem1052184 : term32 = term33.
Proof. exact (fun_ext (fun X : type1272 => @lem1052183 X)). Qed.
Lemma lem1052185 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat))). Qed.
Lemma lem1052186 : term12 = term34.
Proof. exact (MK_COMB (@lem1052185) (@lem1052184)). Qed.
Lemma lem1052187 : (term11 = term12) = (term5 = term34).
Proof. exact (MK_COMB (@lem1052175) (@lem1052186)). Qed.
Lemma lem1052188 : term5 = term34.
Proof. exact (EQ_MP (@lem1052187) (@lem1052162)). Qed.
Lemma lem1052189 : term34.
Proof. exact (EQ_MP (@lem1052188) (@lem1052155)). Qed.
Lemma lem1052191 {A : Type'} : (@ex A) = (term35 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1052192 : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> nat -> nat)) = term36.
Proof. exact (@lem1052191 type1272). Qed.
Lemma lem1052193 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1052194 : term34 = term37.
Proof. exact (MK_COMB (@lem1052192) (@lem1052193)). Qed.
Lemma lem1052195 : term37 = term38.
Proof. exact (eq_refl term37). Qed.
Lemma lem1052196 : term34 = term38.
Proof. exact (TRANS (@lem1052194) (@lem1052195)). Qed.
Lemma lem1052197 : term38.
Proof. exact (EQ_MP (@lem1052196) (@lem1052189)). Qed.
