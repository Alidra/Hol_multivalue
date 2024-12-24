Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_SING_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_EMPTY_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm513079_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3854836 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem3854837 : term1.
Proof. exact (proj2 (@lem3854836)). Qed.
Lemma lem3854838 : term2.
Proof. exact (proj2 (@lem3854837)). Qed.
Lemma lem3854839 : term3.
Proof. exact (proj2 (@lem3854838)). Qed.
Lemma lem3854840 : term4.
Proof. exact (proj2 (@lem3854839)). Qed.
Lemma lem3854841 : term5.
Proof. exact (proj2 (@lem3854840)). Qed.
Lemma lem3854842 : term6.
Proof. exact (proj2 (@lem3854841)). Qed.
Lemma lem3854843 : term7.
Proof. exact (proj2 (@lem3854842)). Qed.
Lemma lem3854844 : term8.
Proof. exact (proj2 (@lem3854843)). Qed.
Lemma lem3854845 : term9.
Proof. exact (proj2 (@lem3854844)). Qed.
Lemma lem3854846 (m : nat) : term10 m.
Proof. exact (@lem3854845 m). Qed.
Lemma lem3854847 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem3854848 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem3854847 m) (@lem3854846 m)). Qed.
Lemma lem3854849 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem3854848 m n). Qed.
Lemma lem3854850 (m : nat) (n : nat) : (term12 m n) = (((BIT1 m) = (BIT1 n)) = (m = n)).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem3854890 : term13.
Proof. exact (proj1 (@lem3854836)). Qed.
Lemma lem3854891 (m : nat) : term14 m.
Proof. exact (@lem3854890 m). Qed.
Lemma lem3854892 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem3854893 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem3854892 m) (@lem3854891 m)). Qed.
Lemma lem3854894 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem3854893 m n). Qed.
Lemma lem3854895 (m : nat) (n : nat) : (term16 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem3855128 : term17.
Proof. exact (EQ_MP (@lem513079) (@lem0)). Qed.
Lemma lem3855129 : term18.
Proof. exact (proj2 (@lem3855128)). Qed.
Lemma lem3855140 : term19.
Proof. exact (proj1 (@lem3855128)). Qed.
Lemma lem3855141 (n : nat) : term20 n.
Proof. exact (@lem3855140 n). Qed.
Lemma lem3855142 (n : nat) : (term20 n) = ((term21 n) = (term22 n)).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem3855147 {A : Type'} (x : A) : term23 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3855148 {A : Type'} (x : A) : (term23 A x) = (term24 A x).
Proof. exact (eq_refl (term23 A x)). Qed.
Lemma lem3855149 {A : Type'} (x : A) : term24 A x.
Proof. exact (EQ_MP (@lem3855148 A x) (@lem3855147 A x)). Qed.
Lemma lem3855150 {A : Type'} (x : A) : term25 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3855152 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem3855160 {A : Type'} : term26 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3855161 {A : Type'} (x : A) : term27 A x.
Proof. exact (@lem3855160 A x). Qed.
Lemma lem3855162 {A : Type'} (x : A) : (term27 A x) = (term28 A x).
Proof. exact (eq_refl (term27 A x)). Qed.
Lemma lem3855163 {A : Type'} (x : A) : term28 A x.
Proof. exact (EQ_MP (@lem3855162 A x) (@lem3855161 A x)). Qed.
Lemma lem3855164 {A : Type'} (x : A) (s : A -> Prop) : term29 A x s.
Proof. exact (@lem3855163 A x s). Qed.
Lemma lem3855165 {A : Type'} (x : A) (s : A -> Prop) : (term29 A x s) = (term30 A x s).
Proof. exact (eq_refl (term29 A x s)). Qed.
Lemma lem3855166 {A : Type'} (x : A) (s : A -> Prop) : term30 A x s.
Proof. exact (EQ_MP (@lem3855165 A x s) (@lem3855164 A x s)). Qed.
Lemma lem3855167 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3855168 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term31 A x s) = (term32 A x s).
Proof. exact (@lem3855166 A x s (@lem3855167 A s h1)). Qed.
Lemma lem3855182 {A : Type'} (x : A) (s : A -> Prop) : term30 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3855168 A x s h0). Qed.
Lemma lem3855183 {A : Type'} (x : A) (s : A -> Prop) : term30 A x s.
Proof. exact (@lem3855182 A x s). Qed.
Lemma lem3855184 {A : Type'} (a : A) : term33 A a.
Proof. exact (@lem3855183 A a (@EMPTY A)). Qed.
Lemma lem3855186 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem3855152 _92140) (@lem3596285 _92140)). Qed.
Lemma lem3855187 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (@lem3855186 A). Qed.
Lemma lem3855188 {A : Type'} : True = (@FINITE A (@EMPTY A)).
Proof. exact (SYM (@lem3855187 A)). Qed.
Lemma lem3855189 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (EQ_MP (@lem3855188 A) (@lem0)). Qed.
Lemma lem3855190 {A : Type'} (a : A) : (term34 A a) = (term35 A a).
Proof. exact (@lem3855184 A a (@lem3855189 A)). Qed.
Lemma lem3855192 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term36 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3855193 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term37 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3855192 _2963 g t e g' t' e'). Qed.
Lemma lem3855194 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term38 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3855193 _2963 g t e g' t'). Qed.
Lemma lem3855195 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term39 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3855194 _2963 g t e g'). Qed.
Lemma lem3855196 (g : Prop) (t : nat) (e : nat) : term40 g t e.
Proof. exact (@lem3855195 nat g t e). Qed.
Lemma lem3855197 {A : Type'} (a : A) : term41 A a.
Proof. exact (@lem3855196 (@IN A a (@EMPTY A)) (@CARD A (@EMPTY A)) (term42 A)). Qed.
Lemma lem3855198 {A : Type'} (a : A) (g' : Prop) : term43 A a g'.
Proof. exact (@lem3855197 A a g'). Qed.
Lemma lem3855199 {A : Type'} (a : A) (g' : Prop) : (term43 A a g') = (term44 A a g').
Proof. exact (eq_refl (term43 A a g')). Qed.
Lemma lem3855200 {A : Type'} (a : A) (g' : Prop) : term44 A a g'.
Proof. exact (EQ_MP (@lem3855199 A a g') (@lem3855198 A a g')). Qed.
Lemma lem3855201 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term45 A a g' t'.
Proof. exact (@lem3855200 A a g' t'). Qed.
Lemma lem3855202 {A : Type'} (a : A) (g' : Prop) (t' : nat) : (term45 A a g' t') = (term46 A a g' t').
Proof. exact (eq_refl (term45 A a g' t')). Qed.
Lemma lem3855203 {A : Type'} (a : A) (g' : Prop) (t' : nat) : term46 A a g' t'.
Proof. exact (EQ_MP (@lem3855202 A a g' t') (@lem3855201 A a g' t')). Qed.
Lemma lem3855204 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term47 A a g' t' e'.
Proof. exact (@lem3855203 A a g' t' e'). Qed.
Lemma lem3855205 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : (term47 A a g' t' e') = (term48 A a g' t' e').
Proof. exact (eq_refl (term47 A a g' t' e')). Qed.
Lemma lem3855206 {A : Type'} (a : A) (g' : Prop) (t' : nat) (e' : nat) : term48 A a g' t' e'.
Proof. exact (EQ_MP (@lem3855205 A a g' t' e') (@lem3855204 A a g' t' e')). Qed.
Lemma lem3855208 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3855150 A x (@lem3855149 A x)). Qed.
Lemma lem3855209 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3855208 A x). Qed.
Lemma lem3855210 {A : Type'} (a : A) : (@IN A a (@EMPTY A)) = False.
Proof. exact (@lem3855209 A a). Qed.
Lemma lem3855211 {A : Type'} (a : A) (t' : nat) (e' : nat) : term49 A a t' e'.
Proof. exact (@lem3855206 A a False t' e'). Qed.
Lemma lem3855212 {A : Type'} (a : A) (t' : nat) (e' : nat) : term50 A a t' e'.
Proof. exact (@lem3855211 A a t' e' (@lem3855210 A a)). Qed.
Lemma lem3855217 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3855218 {A : Type'} : term51 A.
Proof. exact (fun h0 : False => @lem3855217 A). Qed.
Lemma lem3855219 {A : Type'} (a : A) (e' : nat) : term52 A a e'.
Proof. exact (@lem3855212 A a (NUMERAL 0) e'). Qed.
Lemma lem3855220 {A : Type'} (a : A) (e' : nat) : term53 A a e'.
Proof. exact (@lem3855219 A a e' (@lem3855218 A)). Qed.
Lemma lem3855227 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3855228 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem3855229 {A : Type'} : (term42 A) = term54.
Proof. exact (MK_COMB (@lem3855228) (@lem3855227 A)). Qed.
Lemma lem3855231 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem3855142 n) (@lem3855141 n)). Qed.
Lemma lem3855232 : term54 = term55.
Proof. exact (@lem3855231 0). Qed.
Lemma lem3855234 : (S 0) = (BIT1 0).
Proof. exact (proj1 (@lem3855129)). Qed.
Lemma lem3855235 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem3855236 : term55 = term56.
Proof. exact (MK_COMB (@lem3855235) (@lem3855234)). Qed.
Lemma lem3855237 : term54 = term56.
Proof. exact (TRANS (@lem3855232) (@lem3855236)). Qed.
Lemma lem3855238 {A : Type'} : (term42 A) = term56.
Proof. exact (TRANS (@lem3855229 A) (@lem3855237)). Qed.
Lemma lem3855239 {A : Type'} : term57 A.
Proof. exact (fun h0 : ~ False => @lem3855238 A). Qed.
Lemma lem3855240 {A : Type'} (a : A) : term58 A a.
Proof. exact (@lem3855220 A a term56). Qed.
Lemma lem3855241 {A : Type'} (a : A) : (term35 A a) = term59.
Proof. exact (@lem3855240 A a (@lem3855239 A)). Qed.
Lemma lem3855243 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3855244 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3855243 nat t1 t2). Qed.
Lemma lem3855245 : term59 = term56.
Proof. exact (@lem3855244 (NUMERAL 0) term56). Qed.
Lemma lem3855246 {A : Type'} (a : A) : (term35 A a) = term56.
Proof. exact (TRANS (@lem3855241 A a) (@lem3855245)). Qed.
Lemma lem3855247 {A : Type'} (a : A) : (term34 A a) = term56.
Proof. exact (TRANS (@lem3855190 A a) (@lem3855246 A a)). Qed.
Lemma lem3855248 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3855249 {A : Type'} (a : A) : (term60 A a) = term61.
Proof. exact (MK_COMB (@lem3855248) (@lem3855247 A a)). Qed.
Lemma lem3855250 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem3855251 {A : Type'} (a : A) : ((term34 A a) = term56) = (term56 = term56).
Proof. exact (MK_COMB (@lem3855249 A a) (@lem3855250)). Qed.
Lemma lem3855253 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem3854895 m n) (@lem3854894 m n)). Qed.
Lemma lem3855254 : (term56 = term56) = ((BIT1 0) = (BIT1 0)).
Proof. exact (@lem3855253 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3855256 (m : nat) (n : nat) : ((BIT1 m) = (BIT1 n)) = (m = n).
Proof. exact (EQ_MP (@lem3854850 m n) (@lem3854849 m n)). Qed.
Lemma lem3855257 : ((BIT1 0) = (BIT1 0)) = (0 = 0).
Proof. exact (@lem3855256 0 0). Qed.
Lemma lem3855259 : (0 = 0) = True.
Proof. exact (proj1 (@lem3854837)). Qed.
Lemma lem3855260 : ((BIT1 0) = (BIT1 0)) = True.
Proof. exact (TRANS (@lem3855257) (@lem3855259)). Qed.
Lemma lem3855261 : (term56 = term56) = True.
Proof. exact (TRANS (@lem3855254) (@lem3855260)). Qed.
Lemma lem3855262 {A : Type'} (a : A) : ((term34 A a) = term56) = True.
Proof. exact (TRANS (@lem3855251 A a) (@lem3855261)). Qed.
Lemma lem3855263 {A : Type'} : (term62 A) = (term63 A).
Proof. exact (fun_ext (fun a : A => @lem3855262 A a)). Qed.
Lemma lem3855264 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3855265 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (MK_COMB (@lem3855264 A) (@lem3855263 A)). Qed.
Lemma lem3855267 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3855268 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (@lem3855267 A t). Qed.
Lemma lem3855269 {A : Type'} : (term65 A) = True.
Proof. exact (@lem3855268 A True). Qed.
Lemma lem3855270 {A : Type'} : (term64 A) = True.
Proof. exact (TRANS (@lem3855265 A) (@lem3855269 A)). Qed.
Lemma lem3855271 {A : Type'} : True = (term64 A).
Proof. exact (SYM (@lem3855270 A)). Qed.
Lemma lem3855272 {A : Type'} : term64 A.
Proof. exact (EQ_MP (@lem3855271 A) (@lem0)). Qed.
