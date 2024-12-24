Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_POW_term_abbrevs.
Require Import REAL_ZPOW_NEG_spec.
Require Import REAL_ZPOW_NUM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3174158 (x : real) : term0 x.
Proof. exact (@lem3169304 x). Qed.
Lemma lem3174159 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3174160 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3174159 x) (@lem3174158 x)). Qed.
Lemma lem3174161 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem3174160 x n). Qed.
Lemma lem3174162 (x : real) (n : nat) : (term2 x n) = ((term3 x n) = (real_pow x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem3174164 (x : real) : term4 x.
Proof. exact (@lem3173052 x). Qed.
Lemma lem3174165 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3174166 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem3174165 x) (@lem3174164 x)). Qed.
Lemma lem3174167 (x : real) (n : int) : term6 x n.
Proof. exact (@lem3174166 x n). Qed.
Lemma lem3174168 (x : real) (n : int) : (term6 x n) = ((term7 x n) = (term8 x n)).
Proof. exact (eq_refl (term6 x n)). Qed.
Lemma lem3174183 (x : real) (n : nat) : (term3 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174162 x n) (@lem3174161 x n)). Qed.
Lemma lem3174184 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174185 (x : real) (n : nat) : (term9 x n) = (term10 x n).
Proof. exact (MK_COMB (@lem3174184) (@lem3174183 x n)). Qed.
Lemma lem3174186 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem3174187 (x : real) (n : nat) : ((term3 x n) = (real_pow x n)) = ((real_pow x n) = (real_pow x n)).
Proof. exact (MK_COMB (@lem3174185 x n) (@lem3174186 x n)). Qed.
Lemma lem3174189 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3174190 (x : real) : (x = x) = True.
Proof. exact (@lem3174189 real x). Qed.
Lemma lem3174191 (x : real) (n : nat) : ((real_pow x n) = (real_pow x n)) = True.
Proof. exact (@lem3174190 (real_pow x n)). Qed.
Lemma lem3174192 (x : real) (n : nat) : ((term3 x n) = (real_pow x n)) = True.
Proof. exact (TRANS (@lem3174187 x n) (@lem3174191 x n)). Qed.
Lemma lem3174193 (x : real) : (term11 x) = term12.
Proof. exact (fun_ext (fun n : nat => @lem3174192 x n)). Qed.
Lemma lem3174194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174195 (x : real) : (term1 x) = term13.
Proof. exact (MK_COMB (@lem3174194) (@lem3174193 x)). Qed.
Lemma lem3174197 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174198 (t : Prop) : (term15 t) = t.
Proof. exact (@lem3174197 nat t). Qed.
Lemma lem3174199 : term13 = True.
Proof. exact (@lem3174198 True). Qed.
Lemma lem3174200 (x : real) : (term1 x) = True.
Proof. exact (TRANS (@lem3174195 x) (@lem3174199)). Qed.
Lemma lem3174201 : term16 = term17.
Proof. exact (fun_ext (fun x : real => @lem3174200 x)). Qed.
Lemma lem3174202 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3174203 : term18 = term19.
Proof. exact (MK_COMB (@lem3174202) (@lem3174201)). Qed.
Lemma lem3174205 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174206 (t : Prop) : (term20 t) = t.
Proof. exact (@lem3174205 real t). Qed.
Lemma lem3174207 : term19 = True.
Proof. exact (@lem3174206 True). Qed.
Lemma lem3174208 : term18 = True.
Proof. exact (TRANS (@lem3174203) (@lem3174207)). Qed.
Lemma lem3174209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3174210 : term21 = (and True).
Proof. exact (MK_COMB (@lem3174209) (@lem3174208)). Qed.
Lemma lem3174222 (x : real) (n : int) : (term7 x n) = (term8 x n).
Proof. exact (EQ_MP (@lem3174168 x n) (@lem3174167 x n)). Qed.
Lemma lem3174223 (x : real) (n : nat) : (term22 x n) = (term23 x n).
Proof. exact (@lem3174222 x (int_of_num n)). Qed.
Lemma lem3174225 (x : real) (n : nat) : (term3 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3174162 x n) (@lem3174161 x n)). Qed.
Lemma lem3174226 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3174227 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (MK_COMB (@lem3174226) (@lem3174225 x n)). Qed.
Lemma lem3174228 (x : real) (n : nat) : (term22 x n) = (term24 x n).
Proof. exact (TRANS (@lem3174223 x n) (@lem3174227 x n)). Qed.
Lemma lem3174229 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3174230 (x : real) (n : nat) : (term25 x n) = (term26 x n).
Proof. exact (MK_COMB (@lem3174229) (@lem3174228 x n)). Qed.
Lemma lem3174231 (x : real) (n : nat) : (term24 x n) = (term24 x n).
Proof. exact (eq_refl (term24 x n)). Qed.
Lemma lem3174232 (x : real) (n : nat) : ((term22 x n) = (term24 x n)) = ((term24 x n) = (term24 x n)).
Proof. exact (MK_COMB (@lem3174230 x n) (@lem3174231 x n)). Qed.
Lemma lem3174234 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3174235 (x : real) : (x = x) = True.
Proof. exact (@lem3174234 real x). Qed.
Lemma lem3174236 (x : real) (n : nat) : ((term24 x n) = (term24 x n)) = True.
Proof. exact (@lem3174235 (term24 x n)). Qed.
Lemma lem3174237 (x : real) (n : nat) : ((term22 x n) = (term24 x n)) = True.
Proof. exact (TRANS (@lem3174232 x n) (@lem3174236 x n)). Qed.
Lemma lem3174238 (x : real) : (term27 x) = term12.
Proof. exact (fun_ext (fun n : nat => @lem3174237 x n)). Qed.
Lemma lem3174239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3174240 (x : real) : (term28 x) = term13.
Proof. exact (MK_COMB (@lem3174239) (@lem3174238 x)). Qed.
Lemma lem3174242 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174243 (t : Prop) : (term15 t) = t.
Proof. exact (@lem3174242 nat t). Qed.
Lemma lem3174244 : term13 = True.
Proof. exact (@lem3174243 True). Qed.
Lemma lem3174245 (x : real) : (term28 x) = True.
Proof. exact (TRANS (@lem3174240 x) (@lem3174244)). Qed.
Lemma lem3174246 : term29 = term17.
Proof. exact (fun_ext (fun x : real => @lem3174245 x)). Qed.
Lemma lem3174247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3174248 : term30 = term19.
Proof. exact (MK_COMB (@lem3174247) (@lem3174246)). Qed.
Lemma lem3174250 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3174251 (t : Prop) : (term20 t) = t.
Proof. exact (@lem3174250 real t). Qed.
Lemma lem3174252 : term19 = True.
Proof. exact (@lem3174251 True). Qed.
Lemma lem3174253 : term30 = True.
Proof. exact (TRANS (@lem3174248) (@lem3174252)). Qed.
Lemma lem3174254 : term31 = (True /\ True).
Proof. exact (MK_COMB (@lem3174210) (@lem3174253)). Qed.
Lemma lem3174256 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3174257 : (True /\ True) = True.
Proof. exact (@lem3174256 True). Qed.
Lemma lem3174258 : term31 = True.
Proof. exact (TRANS (@lem3174254) (@lem3174257)). Qed.
Lemma lem3174259 : True = term31.
Proof. exact (SYM (@lem3174258)). Qed.
Lemma lem3174260 : term31.
Proof. exact (EQ_MP (@lem3174259) (@lem0)). Qed.
