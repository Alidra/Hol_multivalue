Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLAUSES_RIGHT_term_abbrevs.
Require Import LT_REFL_spec.
Require Import NSUM_CLAUSES_NUMSEG_spec.
Require Import SUC_SUB1_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem7052038 (n : nat) : term0 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem7052039 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7052041 (f : nat -> nat) : term2 f.
Proof. exact (proj2 (@lem7047279 f)). Qed.
Lemma lem7052042 (f : nat -> nat) (m : nat) : term3 f m.
Proof. exact (@lem7052041 f m). Qed.
Lemma lem7052043 (m : nat) (f : nat -> nat) : (term3 f m) = (term4 m f).
Proof. exact (eq_refl (term3 f m)). Qed.
Lemma lem7052044 (m : nat) (f : nat -> nat) : term4 m f.
Proof. exact (EQ_MP (@lem7052043 m f) (@lem7052042 f m)). Qed.
Lemma lem7052045 (m : nat) (f : nat -> nat) (n : nat) : term5 m f n.
Proof. exact (@lem7052044 m f n). Qed.
Lemma lem7052046 (m : nat) (n : nat) (f : nat -> nat) : (term5 m f n) = ((term6 m n f) = (term7 m n f)).
Proof. exact (eq_refl (term5 m f n)). Qed.
Lemma lem7052048 (f : nat -> nat) : term8 f.
Proof. exact (proj1 (@lem7047279 f)). Qed.
Lemma lem7052049 (f : nat -> nat) (m : nat) : term9 f m.
Proof. exact (@lem7052048 f m). Qed.
Lemma lem7052050 (m : nat) (f : nat -> nat) : (term9 f m) = ((term10 m f) = (term11 m f)).
Proof. exact (eq_refl (term9 f m)). Qed.
Lemma lem7052052 (n : nat) : term12 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem7052053 (n : nat) : (term12 n) = (term13 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem7052054 (n : nat) : term13 n.
Proof. exact (EQ_MP (@lem7052053 n) (@lem7052052 n)). Qed.
Lemma lem7052055 (n : nat) : term14 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem7052058 (P : nat -> Prop) : term15 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem7052059 (m : nat) (f : nat -> nat) : term16 m f.
Proof. exact (@lem7052058 (term17 m f)). Qed.
Lemma lem7052060 (m : nat) (f : nat -> nat) : (term18 m f) = (term19 m f).
Proof. exact (eq_refl (term18 m f)). Qed.
Lemma lem7052061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7052062 (m : nat) (f : nat -> nat) : (term20 m f) = (term21 m f).
Proof. exact (MK_COMB (@lem7052061) (@lem7052060 m f)). Qed.
Lemma lem7052063 (m : nat) (f : nat -> nat) (n : nat) : (term22 m f n) = (term23 m f n).
Proof. exact (eq_refl (term22 m f n)). Qed.
Lemma lem7052064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7052065 (m : nat) (f : nat -> nat) (n : nat) : (term24 m f n) = (term25 m f n).
Proof. exact (MK_COMB (@lem7052064) (@lem7052063 m f n)). Qed.
Lemma lem7052066 (m : nat) (f : nat -> nat) (n : nat) : (term26 m f n) = (term27 m f n).
Proof. exact (eq_refl (term26 m f n)). Qed.
Lemma lem7052067 (m : nat) (f : nat -> nat) (n : nat) : (term28 m f n) = (term29 m f n).
Proof. exact (MK_COMB (@lem7052065 m f n) (@lem7052066 m f n)). Qed.
Lemma lem7052068 (m : nat) (f : nat -> nat) : (term30 m f) = (term31 m f).
Proof. exact (fun_ext (fun n : nat => @lem7052067 m f n)). Qed.
Lemma lem7052069 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052070 (m : nat) (f : nat -> nat) : (term32 m f) = (term33 m f).
Proof. exact (MK_COMB (@lem7052069) (@lem7052068 m f)). Qed.
Lemma lem7052071 (m : nat) (f : nat -> nat) : (term34 m f) = (term35 m f).
Proof. exact (MK_COMB (@lem7052062 m f) (@lem7052070 m f)). Qed.
Lemma lem7052072 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7052073 (m : nat) (f : nat -> nat) : (term36 m f) = (term37 m f).
Proof. exact (MK_COMB (@lem7052072) (@lem7052071 m f)). Qed.
Lemma lem7052074 (m : nat) (f : nat -> nat) (n : nat) : (term22 m f n) = (term23 m f n).
Proof. exact (eq_refl (term22 m f n)). Qed.
Lemma lem7052075 (m : nat) (f : nat -> nat) : (term38 m f) = (term17 m f).
Proof. exact (fun_ext (fun n : nat => @lem7052074 m f n)). Qed.
Lemma lem7052076 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7052077 (m : nat) (f : nat -> nat) : (term39 m f) = (term40 m f).
Proof. exact (MK_COMB (@lem7052076) (@lem7052075 m f)). Qed.
Lemma lem7052078 (m : nat) (f : nat -> nat) : (term16 m f) = (term41 m f).
Proof. exact (MK_COMB (@lem7052073 m f) (@lem7052077 m f)). Qed.
Lemma lem7052079 (m : nat) (f : nat -> nat) : term41 m f.
Proof. exact (EQ_MP (@lem7052078 m f) (@lem7052059 m f)). Qed.
Lemma lem7052084 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7052085 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem7052084 p q p' q'). Qed.
Lemma lem7052086 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem7052085 p q p'). Qed.
Lemma lem7052087 (m : nat) (f : nat -> nat) : term45 m f.
Proof. exact (@lem7052086 (term46 m) ((term10 m f) = (term47 m f))). Qed.
Lemma lem7052088 (m : nat) (f : nat -> nat) (p' : Prop) : term48 m f p'.
Proof. exact (@lem7052087 m f p'). Qed.
Lemma lem7052089 (m : nat) (f : nat -> nat) (p' : Prop) : (term48 m f p') = (term49 m f p').
Proof. exact (eq_refl (term48 m f p')). Qed.
Lemma lem7052090 (m : nat) (f : nat -> nat) (p' : Prop) : term49 m f p'.
Proof. exact (EQ_MP (@lem7052089 m f p') (@lem7052088 m f p')). Qed.
Lemma lem7052091 (m : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term50 m f p' q'.
Proof. exact (@lem7052090 m f p' q'). Qed.
Lemma lem7052092 (m : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : (term50 m f p' q') = (term51 m f p' q').
Proof. exact (eq_refl (term50 m f p' q')). Qed.
Lemma lem7052093 (m : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term51 m f p' q'.
Proof. exact (EQ_MP (@lem7052092 m f p' q') (@lem7052091 m f p' q')). Qed.
Lemma lem7052097 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem7052055 n (@lem7052054 n)). Qed.
Lemma lem7052098 : term52 = False.
Proof. exact (@lem7052097 (NUMERAL 0)). Qed.
Lemma lem7052099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7052100 : term53 = (and False).
Proof. exact (MK_COMB (@lem7052099) (@lem7052098)). Qed.
Lemma lem7052101 (m : nat) : (term54 m) = (term54 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem7052102 (m : nat) : (term46 m) = (term55 m).
Proof. exact (MK_COMB (@lem7052100) (@lem7052101 m)). Qed.
Lemma lem7052104 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem7052105 (m : nat) : (term55 m) = False.
Proof. exact (@lem7052104 (term54 m)). Qed.
Lemma lem7052106 (m : nat) : (term46 m) = False.
Proof. exact (TRANS (@lem7052102 m) (@lem7052105 m)). Qed.
Lemma lem7052107 (m : nat) (f : nat -> nat) (q' : Prop) : term56 m f q'.
Proof. exact (@lem7052093 m f False q'). Qed.
Lemma lem7052108 (m : nat) (f : nat -> nat) (q' : Prop) : term57 m f q'.
Proof. exact (@lem7052107 m f q' (@lem7052106 m)). Qed.
Lemma lem7052115 (m : nat) (f : nat -> nat) : (term10 m f) = (term11 m f).
Proof. exact (EQ_MP (@lem7052050 m f) (@lem7052049 f m)). Qed.
Lemma lem7052164 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052165 (m : nat) (f : nat -> nat) : (term58 m f) = (term59 m f).
Proof. exact (MK_COMB (@lem7052164) (@lem7052115 m f)). Qed.
Lemma lem7052214 (m : nat) (f : nat -> nat) : (term47 m f) = (term47 m f).
Proof. exact (eq_refl (term47 m f)). Qed.
Lemma lem7052215 (m : nat) (f : nat -> nat) : ((term10 m f) = (term47 m f)) = ((term11 m f) = (term47 m f)).
Proof. exact (MK_COMB (@lem7052165 m f) (@lem7052214 m f)). Qed.
Lemma lem7052266 (m : nat) (f : nat -> nat) : term60 m f.
Proof. exact (fun h0 : False => @lem7052215 m f). Qed.
Lemma lem7052267 (m : nat) (f : nat -> nat) : term61 m f.
Proof. exact (@lem7052108 m f ((term11 m f) = (term47 m f))). Qed.
Lemma lem7052268 (m : nat) (f : nat -> nat) : (term19 m f) = (term62 m f).
Proof. exact (@lem7052267 m f (@lem7052266 m f)). Qed.
Lemma lem7052270 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7052271 (m : nat) (f : nat -> nat) : (term62 m f) = True.
Proof. exact (@lem7052270 ((term11 m f) = (term47 m f))). Qed.
Lemma lem7052272 (m : nat) (f : nat -> nat) : (term19 m f) = True.
Proof. exact (TRANS (@lem7052268 m f) (@lem7052271 m f)). Qed.
Lemma lem7052273 (m : nat) (f : nat -> nat) : True = (term19 m f).
Proof. exact (SYM (@lem7052272 m f)). Qed.
Lemma lem7052274 (m : nat) (f : nat -> nat) : term19 m f.
Proof. exact (EQ_MP (@lem7052273 m f) (@lem0)). Qed.
Lemma lem7052278 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7052279 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem7052278 p q p' q'). Qed.
Lemma lem7052280 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem7052279 p q p'). Qed.
Lemma lem7052281 (m : nat) (f : nat -> nat) (n : nat) : term63 m f n.
Proof. exact (@lem7052280 (term64 m n) ((term6 m n f) = (term65 m f n))). Qed.
Lemma lem7052282 (m : nat) (f : nat -> nat) (n : nat) (p' : Prop) : term66 m f n p'.
Proof. exact (@lem7052281 m f n p'). Qed.
Lemma lem7052283 (m : nat) (f : nat -> nat) (n : nat) (p' : Prop) : (term66 m f n p') = (term67 m f n p').
Proof. exact (eq_refl (term66 m f n p')). Qed.
Lemma lem7052284 (m : nat) (f : nat -> nat) (n : nat) (p' : Prop) : term67 m f n p'.
Proof. exact (EQ_MP (@lem7052283 m f n p') (@lem7052282 m f n p')). Qed.
Lemma lem7052285 (m : nat) (f : nat -> nat) (n : nat) (p' : Prop) (q' : Prop) : term68 m f n p' q'.
Proof. exact (@lem7052284 m f n p' q'). Qed.
Lemma lem7052286 (m : nat) (f : nat -> nat) (n : nat) (p' : Prop) (q' : Prop) : (term68 m f n p' q') = (term69 m f n p' q').
Proof. exact (eq_refl (term68 m f n p' q')). Qed.
Lemma lem7052287 (m : nat) (f : nat -> nat) (n : nat) (p' : Prop) (q' : Prop) : term69 m f n p' q'.
Proof. exact (EQ_MP (@lem7052286 m f n p' q') (@lem7052285 m f n p' q')). Qed.
Lemma lem7052292 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem7052293 (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term70 f m n q'.
Proof. exact (@lem7052287 m f n (term64 m n) q'). Qed.
Lemma lem7052294 (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term71 f m n q'.
Proof. exact (@lem7052293 f m n q' (@lem7052292 m n)). Qed.
Lemma lem7052295 (m : nat) (n : nat) (h1 : term64 m n) : term64 m n.
Proof. exact (h1). Qed.
Lemma lem7052296 (m : nat) (n : nat) (h1 : term64 m n) : term72 m n.
Proof. exact (proj2 (@lem7052295 m n h1)). Qed.
Lemma lem7052297 (m : nat) (n : nat) : (term72 m n) = ((term72 m n) = True).
Proof. exact (@lem7 (term72 m n)). Qed.
Lemma lem7052305 (m : nat) (n : nat) (f : nat -> nat) : (term6 m n f) = (term7 m n f).
Proof. exact (EQ_MP (@lem7052046 m n f) (@lem7052045 m f n)). Qed.
Lemma lem7052307 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term73 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7052308 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term74 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7052307 _2963 g t e g' t' e'). Qed.
Lemma lem7052309 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term75 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7052308 _2963 g t e g' t'). Qed.
Lemma lem7052310 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term76 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7052309 _2963 g t e g'). Qed.
Lemma lem7052311 (g : Prop) (t : nat) (e : nat) : term77 g t e.
Proof. exact (@lem7052310 nat g t e). Qed.
Lemma lem7052312 (m : nat) (n : nat) (f : nat -> nat) : term78 m n f.
Proof. exact (@lem7052311 (term72 m n) (term79 m f n) (term80 m n f)). Qed.
Lemma lem7052313 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) : term81 m n f g'.
Proof. exact (@lem7052312 m n f g'). Qed.
Lemma lem7052314 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) : (term81 m n f g') = (term82 m n f g').
Proof. exact (eq_refl (term81 m n f g')). Qed.
Lemma lem7052315 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) : term82 m n f g'.
Proof. exact (EQ_MP (@lem7052314 m n f g') (@lem7052313 m n f g')). Qed.
Lemma lem7052316 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) : term83 m n f g' t'.
Proof. exact (@lem7052315 m n f g' t'). Qed.
Lemma lem7052317 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) : (term83 m n f g' t') = (term84 m n f g' t').
Proof. exact (eq_refl (term83 m n f g' t')). Qed.
Lemma lem7052318 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) : term84 m n f g' t'.
Proof. exact (EQ_MP (@lem7052317 m n f g' t') (@lem7052316 m n f g' t')). Qed.
Lemma lem7052319 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) (e' : nat) : term85 m n f g' t' e'.
Proof. exact (@lem7052318 m n f g' t' e'). Qed.
Lemma lem7052320 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term85 m n f g' t' e') = (term86 m n f g' t' e').
Proof. exact (eq_refl (term85 m n f g' t' e')). Qed.
Lemma lem7052321 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) (e' : nat) : term86 m n f g' t' e'.
Proof. exact (EQ_MP (@lem7052320 m n f g' t' e') (@lem7052319 m n f g' t' e')). Qed.
Lemma lem7052323 (m : nat) (n : nat) (h1 : term64 m n) : (term72 m n) = True.
Proof. exact (EQ_MP (@lem7052297 m n) (@lem7052296 m n h1)). Qed.
Lemma lem7052324 (m : nat) (n : nat) (f : nat -> nat) (t' : nat) (e' : nat) : term87 m n f t' e'.
Proof. exact (@lem7052321 m n f True t' e'). Qed.
Lemma lem7052325 (f : nat -> nat) (t' : nat) (e' : nat) (m : nat) (n : nat) (h1 : term64 m n) : term88 m n f t' e'.
Proof. exact (@lem7052324 m n f t' e' (@lem7052323 m n h1)). Qed.
Lemma lem7052331 (m : nat) (f : nat -> nat) (n : nat) : (term79 m f n) = (term79 m f n).
Proof. exact (eq_refl (term79 m f n)). Qed.
Lemma lem7052332 (m : nat) (f : nat -> nat) (n : nat) : term89 m f n.
Proof. exact (fun h0 : True => @lem7052331 m f n). Qed.
Lemma lem7052333 (f : nat -> nat) (e' : nat) (m : nat) (n : nat) (h1 : term64 m n) : term90 m f n e'.
Proof. exact (@lem7052325 f (term79 m f n) e' m n h1). Qed.
Lemma lem7052334 (f : nat -> nat) (e' : nat) (m : nat) (n : nat) (h1 : term64 m n) : term91 m f n e'.
Proof. exact (@lem7052333 f e' m n h1 (@lem7052332 m f n)). Qed.
Lemma lem7052338 (m : nat) (n : nat) (f : nat -> nat) : (term80 m n f) = (term80 m n f).
Proof. exact (eq_refl (term80 m n f)). Qed.
Lemma lem7052339 (m : nat) (n : nat) (f : nat -> nat) : term92 m n f.
Proof. exact (fun h0 : ~ True => @lem7052338 m n f). Qed.
Lemma lem7052340 (f : nat -> nat) (m : nat) (n : nat) (h1 : term64 m n) : term93 m n f.
Proof. exact (@lem7052334 f (term80 m n f) m n h1). Qed.
Lemma lem7052341 (f : nat -> nat) (m : nat) (n : nat) (h1 : term64 m n) : (term7 m n f) = (term94 m n f).
Proof. exact (@lem7052340 f m n h1 (@lem7052339 m n f)). Qed.
Lemma lem7052343 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7052344 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7052343 nat t2 t1). Qed.
Lemma lem7052345 (m : nat) (f : nat -> nat) (n : nat) : (term94 m n f) = (term79 m f n).
Proof. exact (@lem7052344 (term80 m n f) (term79 m f n)). Qed.
Lemma lem7052346 (f : nat -> nat) (m : nat) (n : nat) (h1 : term64 m n) : (term7 m n f) = (term79 m f n).
Proof. exact (TRANS (@lem7052341 f m n h1) (@lem7052345 m f n)). Qed.
Lemma lem7052347 (f : nat -> nat) (m : nat) (n : nat) (h1 : term64 m n) : (term6 m n f) = (term79 m f n).
Proof. exact (TRANS (@lem7052305 m n f) (@lem7052346 f m n h1)). Qed.
Lemma lem7052348 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7052349 (f : nat -> nat) (m : nat) (n : nat) (h1 : term64 m n) : (term95 m n f) = (term96 m f n).
Proof. exact (MK_COMB (@lem7052348) (@lem7052347 f m n h1)). Qed.
Lemma lem7052351 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem7052039 n) (@lem7052038 n)). Qed.
Lemma lem7052352 (m : nat) : (dotdot m) = (dotdot m).
Proof. exact (eq_refl (dotdot m)). Qed.
Lemma lem7052353 (m : nat) (n : nat) : (term97 m n) = (dotdot m n).
Proof. exact (MK_COMB (@lem7052352 m) (@lem7052351 n)). Qed.
Lemma lem7052354 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7052355 (m : nat) (n : nat) : (term98 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem7052354) (@lem7052353 m n)). Qed.
Lemma lem7052356 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7052357 (m : nat) (n : nat) (f : nat -> nat) : (term100 m n f) = (term80 m n f).
Proof. exact (MK_COMB (@lem7052355 m n) (@lem7052356 f)). Qed.
Lemma lem7052358 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7052359 (m : nat) (n : nat) (f : nat -> nat) : (term101 m n f) = (term102 m n f).
Proof. exact (MK_COMB (@lem7052358) (@lem7052357 m n f)). Qed.
Lemma lem7052360 (f : nat -> nat) (n : nat) : (term103 f n) = (term103 f n).
Proof. exact (eq_refl (term103 f n)). Qed.
Lemma lem7052361 (m : nat) (f : nat -> nat) (n : nat) : (term65 m f n) = (term79 m f n).
Proof. exact (MK_COMB (@lem7052359 m n f) (@lem7052360 f n)). Qed.
Lemma lem7052362 (f : nat -> nat) (m : nat) (n : nat) (h1 : term64 m n) : ((term6 m n f) = (term65 m f n)) = ((term79 m f n) = (term79 m f n)).
Proof. exact (MK_COMB (@lem7052349 f m n h1) (@lem7052361 m f n)). Qed.
Lemma lem7052364 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7052365 (x : nat) : (x = x) = True.
Proof. exact (@lem7052364 nat x). Qed.
Lemma lem7052366 (m : nat) (f : nat -> nat) (n : nat) : ((term79 m f n) = (term79 m f n)) = True.
Proof. exact (@lem7052365 (term79 m f n)). Qed.
Lemma lem7052367 (f : nat -> nat) (m : nat) (n : nat) (h1 : term64 m n) : ((term6 m n f) = (term65 m f n)) = True.
Proof. exact (TRANS (@lem7052362 f m n h1) (@lem7052366 m f n)). Qed.
Lemma lem7052368 (m : nat) (f : nat -> nat) (n : nat) : term104 m f n.
Proof. exact (fun h0 : term64 m n => @lem7052367 f m n h0). Qed.
Lemma lem7052369 (f : nat -> nat) (m : nat) (n : nat) : term105 f m n.
Proof. exact (@lem7052294 f m n True). Qed.
Lemma lem7052370 (f : nat -> nat) (m : nat) (n : nat) : (term27 m f n) = (term106 m n).
Proof. exact (@lem7052369 f m n (@lem7052368 m f n)). Qed.
Lemma lem7052372 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7052373 (m : nat) (n : nat) : (term106 m n) = True.
Proof. exact (@lem7052372 (term64 m n)). Qed.
Lemma lem7052374 (m : nat) (f : nat -> nat) (n : nat) : (term27 m f n) = True.
Proof. exact (TRANS (@lem7052370 f m n) (@lem7052373 m n)). Qed.
Lemma lem7052375 (m : nat) (f : nat -> nat) (n : nat) : True = (term27 m f n).
Proof. exact (SYM (@lem7052374 m f n)). Qed.
Lemma lem7052376 (m : nat) (f : nat -> nat) (n : nat) : term27 m f n.
Proof. exact (EQ_MP (@lem7052375 m f n) (@lem0)). Qed.
Lemma lem7052377 (m : nat) (f : nat -> nat) (n : nat) : term29 m f n.
Proof. exact (fun h0 : term23 m f n => @lem7052376 m f n). Qed.
Lemma lem7052382 (m : nat) (f : nat -> nat) : term33 m f.
Proof. exact (fun n : nat => @lem7052377 m f n). Qed.
Lemma lem7052383 (m : nat) (f : nat -> nat) : term35 m f.
Proof. exact (conj (@lem7052274 m f) (@lem7052382 m f)). Qed.
Lemma lem7052384 (m : nat) (f : nat -> nat) : term40 m f.
Proof. exact (@lem7052079 m f (@lem7052383 m f)). Qed.
Lemma lem7052389 (f : nat -> nat) : term107 f.
Proof. exact (fun m : nat => @lem7052384 m f). Qed.
Lemma lem7052394 : term108.
Proof. exact (fun f : nat -> nat => @lem7052389 f). Qed.
