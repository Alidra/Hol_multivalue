Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_OF_NUM_LE_term_abbrevs.
Require Import BOUNDS_LINEAR_spec.
Require Import NADD_OF_NUM_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1273145 (A : nat) : term0 A.
Proof. exact (@lem1260452 A). Qed.
Lemma lem1273146 (A : nat) : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1273147 (A : nat) : term1 A.
Proof. exact (EQ_MP (@lem1273146 A) (@lem1273145 A)). Qed.
Lemma lem1273148 (A : nat) (B : nat) : term2 A B.
Proof. exact (@lem1273147 A B). Qed.
Lemma lem1273149 (A : nat) (B : nat) : (term2 A B) = (term3 A B).
Proof. exact (eq_refl (term2 A B)). Qed.
Lemma lem1273150 (A : nat) (B : nat) : term3 A B.
Proof. exact (EQ_MP (@lem1273149 A B) (@lem1273148 A B)). Qed.
Lemma lem1273151 (A : nat) (B : nat) (C : nat) : term4 A B C.
Proof. exact (@lem1273150 A B C). Qed.
Lemma lem1273152 (C : nat) (A : nat) (B : nat) : (term4 A B C) = ((term5 A B C) = (Peano.le A B)).
Proof. exact (eq_refl (term4 A B C)). Qed.
Lemma lem1273154 (k : nat) : term6 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1273155 (k : nat) : (term6 k) = ((term7 k) = (term8 k)).
Proof. exact (eq_refl (term6 k)). Qed.
Lemma lem1273157 (x : nadd) : term9 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1273158 (x : nadd) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1273159 (x : nadd) : term10 x.
Proof. exact (EQ_MP (@lem1273158 x) (@lem1273157 x)). Qed.
Lemma lem1273160 (x : nadd) (y : nadd) : term11 x y.
Proof. exact (@lem1273159 x y). Qed.
Lemma lem1273161 (x : nadd) (y : nadd) : (term11 x y) = ((nadd_le x y) = (term12 x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1273166 (x : nadd) (y : nadd) : (nadd_le x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1273161 x y) (@lem1273160 x y)). Qed.
Lemma lem1273167 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (@lem1273166 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1273177 (k : nat) : (term7 k) = (term8 k).
Proof. exact (EQ_MP (@lem1273155 k) (@lem1273154 k)). Qed.
Lemma lem1273178 (m : nat) : (term7 m) = (term8 m).
Proof. exact (@lem1273177 m). Qed.
Lemma lem1273179 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1273180 (m : nat) (n' : nat) : (term15 m n') = (term16 m n').
Proof. exact (MK_COMB (@lem1273178 m) (@lem1273179 n')). Qed.
Lemma lem1273182 {A B : Type'} (f : A -> B) (y : A) : (term17 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1273183 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem1273182 nat nat f y). Qed.
Lemma lem1273184 (m : nat) (n' : nat) : (term19 m n') = (term16 m n').
Proof. exact (@lem1273183 (term8 m) n'). Qed.
Lemma lem1273185 (m : nat) (n : nat) : (term16 m n) = (Nat.mul m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1273186 (m : nat) : (term20 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem1273185 m n)). Qed.
Lemma lem1273187 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1273188 (m : nat) (n' : nat) : (term19 m n') = (term16 m n').
Proof. exact (MK_COMB (@lem1273186 m) (@lem1273187 n')). Qed.
Lemma lem1273189 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1273190 (m : nat) (n' : nat) : (term21 m n') = (term22 m n').
Proof. exact (MK_COMB (@lem1273189) (@lem1273188 m n')). Qed.
Lemma lem1273191 (m : nat) (n' : nat) : (term16 m n') = (Nat.mul m n').
Proof. exact (eq_refl (term16 m n')). Qed.
Lemma lem1273192 (m : nat) (n' : nat) : ((term19 m n') = (term16 m n')) = ((term16 m n') = (Nat.mul m n')).
Proof. exact (MK_COMB (@lem1273190 m n') (@lem1273191 m n')). Qed.
Lemma lem1273193 (m : nat) (n' : nat) : (term16 m n') = (Nat.mul m n').
Proof. exact (EQ_MP (@lem1273192 m n') (@lem1273184 m n')). Qed.
Lemma lem1273194 (m : nat) (n' : nat) : (term15 m n') = (Nat.mul m n').
Proof. exact (TRANS (@lem1273180 m n') (@lem1273193 m n')). Qed.
Lemma lem1273195 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1273196 (m : nat) (n' : nat) : (term23 m n') = (term24 m n').
Proof. exact (MK_COMB (@lem1273195) (@lem1273194 m n')). Qed.
Lemma lem1273198 (k : nat) : (term7 k) = (term8 k).
Proof. exact (EQ_MP (@lem1273155 k) (@lem1273154 k)). Qed.
Lemma lem1273199 (n : nat) : (term7 n) = (term8 n).
Proof. exact (@lem1273198 n). Qed.
Lemma lem1273200 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1273201 (n : nat) (n' : nat) : (term15 n n') = (term16 n n').
Proof. exact (MK_COMB (@lem1273199 n) (@lem1273200 n')). Qed.
Lemma lem1273203 {A B : Type'} (f : A -> B) (y : A) : (term17 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1273204 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem1273203 nat nat f y). Qed.
Lemma lem1273205 (n : nat) (n' : nat) : (term19 n n') = (term16 n n').
Proof. exact (@lem1273204 (term8 n) n'). Qed.
Lemma lem1273206 (n : nat) (n' : nat) : (term16 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term16 n n')). Qed.
Lemma lem1273207 (n : nat) : (term20 n) = (term8 n).
Proof. exact (fun_ext (fun n' : nat => @lem1273206 n n')). Qed.
Lemma lem1273208 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1273209 (n : nat) (n' : nat) : (term19 n n') = (term16 n n').
Proof. exact (MK_COMB (@lem1273207 n) (@lem1273208 n')). Qed.
Lemma lem1273210 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1273211 (n : nat) (n' : nat) : (term21 n n') = (term22 n n').
Proof. exact (MK_COMB (@lem1273210) (@lem1273209 n n')). Qed.
Lemma lem1273212 (n : nat) (n' : nat) : (term16 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term16 n n')). Qed.
Lemma lem1273213 (n : nat) (n' : nat) : ((term19 n n') = (term16 n n')) = ((term16 n n') = (Nat.mul n n')).
Proof. exact (MK_COMB (@lem1273211 n n') (@lem1273212 n n')). Qed.
Lemma lem1273214 (n : nat) (n' : nat) : (term16 n n') = (Nat.mul n n').
Proof. exact (EQ_MP (@lem1273213 n n') (@lem1273205 n n')). Qed.
Lemma lem1273215 (n : nat) (n' : nat) : (term15 n n') = (Nat.mul n n').
Proof. exact (TRANS (@lem1273201 n n') (@lem1273214 n n')). Qed.
Lemma lem1273216 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1273217 (n : nat) (n' : nat) : (term25 n n') = (term26 n n').
Proof. exact (MK_COMB (@lem1273216) (@lem1273215 n n')). Qed.
Lemma lem1273218 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1273219 (n : nat) (n' : nat) (B : nat) : (term27 n n' B) = (term28 n n' B).
Proof. exact (MK_COMB (@lem1273217 n n') (@lem1273218 B)). Qed.
Lemma lem1273220 (m : nat) (n : nat) (n' : nat) (B : nat) : (term29 m n n' B) = (term30 m n n' B).
Proof. exact (MK_COMB (@lem1273196 m n') (@lem1273219 n n' B)). Qed.
Lemma lem1273221 (m : nat) (n : nat) (B : nat) : (term31 m n B) = (term32 m n B).
Proof. exact (fun_ext (fun n' : nat => @lem1273220 m n n' B)). Qed.
Lemma lem1273222 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1273223 (m : nat) (n : nat) (B : nat) : (term33 m n B) = (term5 m n B).
Proof. exact (MK_COMB (@lem1273222) (@lem1273221 m n B)). Qed.
Lemma lem1273228 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (fun_ext (fun B : nat => @lem1273223 m n B)). Qed.
Lemma lem1273229 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1273230 (m : nat) (n : nat) : (term14 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem1273229) (@lem1273228 m n)). Qed.
Lemma lem1273235 (m : nat) (n : nat) : (term13 m n) = (term36 m n).
Proof. exact (TRANS (@lem1273167 m n) (@lem1273230 m n)). Qed.
Lemma lem1273236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1273237 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem1273236) (@lem1273235 m n)). Qed.
Lemma lem1273238 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1273239 (m : nat) (n : nat) : ((term13 m n) = (Peano.le m n)) = ((term36 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1273237 m n) (@lem1273238 m n)). Qed.
Lemma lem1273242 (m : nat) (n : nat) : ((term36 m n) = (Peano.le m n)) = ((term13 m n) = (Peano.le m n)).
Proof. exact (SYM (@lem1273239 m n)). Qed.
Lemma lem1273250 (C : nat) (A : nat) (B : nat) : (term5 A B C) = (Peano.le A B).
Proof. exact (EQ_MP (@lem1273152 C A B) (@lem1273151 A B C)). Qed.
Lemma lem1273251 (B : nat) (m : nat) (n : nat) : (term5 m n B) = (Peano.le m n).
Proof. exact (@lem1273250 B m n). Qed.
Lemma lem1273252 (m : nat) (n : nat) : (term35 m n) = (term39 m n).
Proof. exact (fun_ext (fun B : nat => @lem1273251 B m n)). Qed.
Lemma lem1273253 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1273254 (m : nat) (n : nat) : (term36 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem1273253) (@lem1273252 m n)). Qed.
Lemma lem1273256 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1273257 (t : Prop) : (term42 t) = t.
Proof. exact (@lem1273256 nat t). Qed.
Lemma lem1273258 (m : nat) (n : nat) : (term40 m n) = (Peano.le m n).
Proof. exact (@lem1273257 (Peano.le m n)). Qed.
Lemma lem1273259 (m : nat) (n : nat) : (term36 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem1273254 m n) (@lem1273258 m n)). Qed.
Lemma lem1273260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1273261 (m : nat) (n : nat) : (term38 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem1273260) (@lem1273259 m n)). Qed.
Lemma lem1273262 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1273263 (m : nat) (n : nat) : ((term36 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1273261 m n) (@lem1273262 m n)). Qed.
Lemma lem1273265 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1273266 (x : Prop) : (x = x) = True.
Proof. exact (@lem1273265 Prop x). Qed.
Lemma lem1273267 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem1273266 (Peano.le m n)). Qed.
Lemma lem1273268 (m : nat) (n : nat) : ((term36 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem1273263 m n) (@lem1273267 m n)). Qed.
Lemma lem1273269 (m : nat) (n : nat) : True = ((term36 m n) = (Peano.le m n)).
Proof. exact (SYM (@lem1273268 m n)). Qed.
Lemma lem1273270 (m : nat) (n : nat) : (term36 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1273269 m n) (@lem0)). Qed.
Lemma lem1273271 (m : nat) (n : nat) : (term13 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1273242 m n) (@lem1273270 m n)). Qed.
Lemma lem1273276 (m : nat) : term44 m.
Proof. exact (fun n : nat => @lem1273271 m n). Qed.
Lemma lem1273281 : term45.
Proof. exact (fun m : nat => @lem1273276 m). Qed.
