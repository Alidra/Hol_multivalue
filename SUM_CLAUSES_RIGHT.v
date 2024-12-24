Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLAUSES_RIGHT_term_abbrevs.
Require Import LT_REFL_spec.
Require Import SUC_SUB1_spec.
Require Import SUM_CLAUSES_NUMSEG_spec.
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
Lemma lem7226009 (n : nat) : term0 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem7226010 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7226012 (f : nat -> real) : term2 f.
Proof. exact (proj2 (@lem7221724 f)). Qed.
Lemma lem7226013 (f : nat -> real) (m : nat) : term3 f m.
Proof. exact (@lem7226012 f m). Qed.
Lemma lem7226014 (m : nat) (f : nat -> real) : (term3 f m) = (term4 m f).
Proof. exact (eq_refl (term3 f m)). Qed.
Lemma lem7226015 (m : nat) (f : nat -> real) : term4 m f.
Proof. exact (EQ_MP (@lem7226014 m f) (@lem7226013 f m)). Qed.
Lemma lem7226016 (m : nat) (f : nat -> real) (n : nat) : term5 m f n.
Proof. exact (@lem7226015 m f n). Qed.
Lemma lem7226017 (m : nat) (n : nat) (f : nat -> real) : (term5 m f n) = ((term6 m n f) = (term7 m n f)).
Proof. exact (eq_refl (term5 m f n)). Qed.
Lemma lem7226019 (f : nat -> real) : term8 f.
Proof. exact (proj1 (@lem7221724 f)). Qed.
Lemma lem7226020 (f : nat -> real) (m : nat) : term9 f m.
Proof. exact (@lem7226019 f m). Qed.
Lemma lem7226021 (m : nat) (f : nat -> real) : (term9 f m) = ((term10 m f) = (term11 m f)).
Proof. exact (eq_refl (term9 f m)). Qed.
Lemma lem7226023 (n : nat) : term12 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem7226024 (n : nat) : (term12 n) = (term13 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem7226025 (n : nat) : term13 n.
Proof. exact (EQ_MP (@lem7226024 n) (@lem7226023 n)). Qed.
Lemma lem7226026 (n : nat) : term14 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem7226029 (P : nat -> Prop) : term15 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem7226030 (m : nat) (f : nat -> real) : term16 m f.
Proof. exact (@lem7226029 (term17 m f)). Qed.
Lemma lem7226031 (m : nat) (f : nat -> real) : (term18 m f) = (term19 m f).
Proof. exact (eq_refl (term18 m f)). Qed.
Lemma lem7226032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7226033 (m : nat) (f : nat -> real) : (term20 m f) = (term21 m f).
Proof. exact (MK_COMB (@lem7226032) (@lem7226031 m f)). Qed.
Lemma lem7226034 (m : nat) (f : nat -> real) (n : nat) : (term22 m f n) = (term23 m f n).
Proof. exact (eq_refl (term22 m f n)). Qed.
Lemma lem7226035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7226036 (m : nat) (f : nat -> real) (n : nat) : (term24 m f n) = (term25 m f n).
Proof. exact (MK_COMB (@lem7226035) (@lem7226034 m f n)). Qed.
Lemma lem7226037 (m : nat) (f : nat -> real) (n : nat) : (term26 m f n) = (term27 m f n).
Proof. exact (eq_refl (term26 m f n)). Qed.
Lemma lem7226038 (m : nat) (f : nat -> real) (n : nat) : (term28 m f n) = (term29 m f n).
Proof. exact (MK_COMB (@lem7226036 m f n) (@lem7226037 m f n)). Qed.
Lemma lem7226039 (m : nat) (f : nat -> real) : (term30 m f) = (term31 m f).
Proof. exact (fun_ext (fun n : nat => @lem7226038 m f n)). Qed.
Lemma lem7226040 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7226041 (m : nat) (f : nat -> real) : (term32 m f) = (term33 m f).
Proof. exact (MK_COMB (@lem7226040) (@lem7226039 m f)). Qed.
Lemma lem7226042 (m : nat) (f : nat -> real) : (term34 m f) = (term35 m f).
Proof. exact (MK_COMB (@lem7226033 m f) (@lem7226041 m f)). Qed.
Lemma lem7226043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7226044 (m : nat) (f : nat -> real) : (term36 m f) = (term37 m f).
Proof. exact (MK_COMB (@lem7226043) (@lem7226042 m f)). Qed.
Lemma lem7226045 (m : nat) (f : nat -> real) (n : nat) : (term22 m f n) = (term23 m f n).
Proof. exact (eq_refl (term22 m f n)). Qed.
Lemma lem7226046 (m : nat) (f : nat -> real) : (term38 m f) = (term17 m f).
Proof. exact (fun_ext (fun n : nat => @lem7226045 m f n)). Qed.
Lemma lem7226047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7226048 (m : nat) (f : nat -> real) : (term39 m f) = (term40 m f).
Proof. exact (MK_COMB (@lem7226047) (@lem7226046 m f)). Qed.
Lemma lem7226049 (m : nat) (f : nat -> real) : (term16 m f) = (term41 m f).
Proof. exact (MK_COMB (@lem7226044 m f) (@lem7226048 m f)). Qed.
Lemma lem7226050 (m : nat) (f : nat -> real) : term41 m f.
Proof. exact (EQ_MP (@lem7226049 m f) (@lem7226030 m f)). Qed.
Lemma lem7226055 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7226056 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem7226055 p q p' q'). Qed.
Lemma lem7226057 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem7226056 p q p'). Qed.
Lemma lem7226058 (m : nat) (f : nat -> real) : term45 m f.
Proof. exact (@lem7226057 (term46 m) ((term10 m f) = (term47 m f))). Qed.
Lemma lem7226059 (m : nat) (f : nat -> real) (p' : Prop) : term48 m f p'.
Proof. exact (@lem7226058 m f p'). Qed.
Lemma lem7226060 (m : nat) (f : nat -> real) (p' : Prop) : (term48 m f p') = (term49 m f p').
Proof. exact (eq_refl (term48 m f p')). Qed.
Lemma lem7226061 (m : nat) (f : nat -> real) (p' : Prop) : term49 m f p'.
Proof. exact (EQ_MP (@lem7226060 m f p') (@lem7226059 m f p')). Qed.
Lemma lem7226062 (m : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term50 m f p' q'.
Proof. exact (@lem7226061 m f p' q'). Qed.
Lemma lem7226063 (m : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : (term50 m f p' q') = (term51 m f p' q').
Proof. exact (eq_refl (term50 m f p' q')). Qed.
Lemma lem7226064 (m : nat) (f : nat -> real) (p' : Prop) (q' : Prop) : term51 m f p' q'.
Proof. exact (EQ_MP (@lem7226063 m f p' q') (@lem7226062 m f p' q')). Qed.
Lemma lem7226068 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem7226026 n (@lem7226025 n)). Qed.
Lemma lem7226069 : term52 = False.
Proof. exact (@lem7226068 (NUMERAL 0)). Qed.
Lemma lem7226070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7226071 : term53 = (and False).
Proof. exact (MK_COMB (@lem7226070) (@lem7226069)). Qed.
Lemma lem7226072 (m : nat) : (term54 m) = (term54 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem7226073 (m : nat) : (term46 m) = (term55 m).
Proof. exact (MK_COMB (@lem7226071) (@lem7226072 m)). Qed.
Lemma lem7226075 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem7226076 (m : nat) : (term55 m) = False.
Proof. exact (@lem7226075 (term54 m)). Qed.
Lemma lem7226077 (m : nat) : (term46 m) = False.
Proof. exact (TRANS (@lem7226073 m) (@lem7226076 m)). Qed.
Lemma lem7226078 (m : nat) (f : nat -> real) (q' : Prop) : term56 m f q'.
Proof. exact (@lem7226064 m f False q'). Qed.
Lemma lem7226079 (m : nat) (f : nat -> real) (q' : Prop) : term57 m f q'.
Proof. exact (@lem7226078 m f q' (@lem7226077 m)). Qed.
Lemma lem7226086 (m : nat) (f : nat -> real) : (term10 m f) = (term11 m f).
Proof. exact (EQ_MP (@lem7226021 m f) (@lem7226020 f m)). Qed.
Lemma lem7226135 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7226136 (m : nat) (f : nat -> real) : (term58 m f) = (term59 m f).
Proof. exact (MK_COMB (@lem7226135) (@lem7226086 m f)). Qed.
Lemma lem7226185 (m : nat) (f : nat -> real) : (term47 m f) = (term47 m f).
Proof. exact (eq_refl (term47 m f)). Qed.
Lemma lem7226186 (m : nat) (f : nat -> real) : ((term10 m f) = (term47 m f)) = ((term11 m f) = (term47 m f)).
Proof. exact (MK_COMB (@lem7226136 m f) (@lem7226185 m f)). Qed.
Lemma lem7226237 (m : nat) (f : nat -> real) : term60 m f.
Proof. exact (fun h0 : False => @lem7226186 m f). Qed.
Lemma lem7226238 (m : nat) (f : nat -> real) : term61 m f.
Proof. exact (@lem7226079 m f ((term11 m f) = (term47 m f))). Qed.
Lemma lem7226239 (m : nat) (f : nat -> real) : (term19 m f) = (term62 m f).
Proof. exact (@lem7226238 m f (@lem7226237 m f)). Qed.
Lemma lem7226241 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem7226242 (m : nat) (f : nat -> real) : (term62 m f) = True.
Proof. exact (@lem7226241 ((term11 m f) = (term47 m f))). Qed.
Lemma lem7226243 (m : nat) (f : nat -> real) : (term19 m f) = True.
Proof. exact (TRANS (@lem7226239 m f) (@lem7226242 m f)). Qed.
Lemma lem7226244 (m : nat) (f : nat -> real) : True = (term19 m f).
Proof. exact (SYM (@lem7226243 m f)). Qed.
Lemma lem7226245 (m : nat) (f : nat -> real) : term19 m f.
Proof. exact (EQ_MP (@lem7226244 m f) (@lem0)). Qed.
Lemma lem7226249 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term42 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7226250 (p : Prop) (q : Prop) (p' : Prop) : term43 p q p'.
Proof. exact (fun q' : Prop => @lem7226249 p q p' q'). Qed.
Lemma lem7226251 (p : Prop) (q : Prop) : term44 p q.
Proof. exact (fun p' : Prop => @lem7226250 p q p'). Qed.
Lemma lem7226252 (m : nat) (f : nat -> real) (n : nat) : term63 m f n.
Proof. exact (@lem7226251 (term64 m n) ((term6 m n f) = (term65 m f n))). Qed.
Lemma lem7226253 (m : nat) (f : nat -> real) (n : nat) (p' : Prop) : term66 m f n p'.
Proof. exact (@lem7226252 m f n p'). Qed.
Lemma lem7226254 (m : nat) (f : nat -> real) (n : nat) (p' : Prop) : (term66 m f n p') = (term67 m f n p').
Proof. exact (eq_refl (term66 m f n p')). Qed.
Lemma lem7226255 (m : nat) (f : nat -> real) (n : nat) (p' : Prop) : term67 m f n p'.
Proof. exact (EQ_MP (@lem7226254 m f n p') (@lem7226253 m f n p')). Qed.
Lemma lem7226256 (m : nat) (f : nat -> real) (n : nat) (p' : Prop) (q' : Prop) : term68 m f n p' q'.
Proof. exact (@lem7226255 m f n p' q'). Qed.
Lemma lem7226257 (m : nat) (f : nat -> real) (n : nat) (p' : Prop) (q' : Prop) : (term68 m f n p' q') = (term69 m f n p' q').
Proof. exact (eq_refl (term68 m f n p' q')). Qed.
Lemma lem7226258 (m : nat) (f : nat -> real) (n : nat) (p' : Prop) (q' : Prop) : term69 m f n p' q'.
Proof. exact (EQ_MP (@lem7226257 m f n p' q') (@lem7226256 m f n p' q')). Qed.
Lemma lem7226263 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem7226264 (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term70 f m n q'.
Proof. exact (@lem7226258 m f n (term64 m n) q'). Qed.
Lemma lem7226265 (f : nat -> real) (m : nat) (n : nat) (q' : Prop) : term71 f m n q'.
Proof. exact (@lem7226264 f m n q' (@lem7226263 m n)). Qed.
Lemma lem7226266 (m : nat) (n : nat) (h1 : term64 m n) : term64 m n.
Proof. exact (h1). Qed.
Lemma lem7226267 (m : nat) (n : nat) (h1 : term64 m n) : term72 m n.
Proof. exact (proj2 (@lem7226266 m n h1)). Qed.
Lemma lem7226268 (m : nat) (n : nat) : (term72 m n) = ((term72 m n) = True).
Proof. exact (@lem7 (term72 m n)). Qed.
Lemma lem7226276 (m : nat) (n : nat) (f : nat -> real) : (term6 m n f) = (term7 m n f).
Proof. exact (EQ_MP (@lem7226017 m n f) (@lem7226016 m f n)). Qed.
Lemma lem7226278 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term73 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7226279 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term74 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7226278 _2963 g t e g' t' e'). Qed.
Lemma lem7226280 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term75 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7226279 _2963 g t e g' t'). Qed.
Lemma lem7226281 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term76 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7226280 _2963 g t e g'). Qed.
Lemma lem7226282 (g : Prop) (t : real) (e : real) : term77 g t e.
Proof. exact (@lem7226281 real g t e). Qed.
Lemma lem7226283 (m : nat) (n : nat) (f : nat -> real) : term78 m n f.
Proof. exact (@lem7226282 (term72 m n) (term79 m f n) (term80 m n f)). Qed.
Lemma lem7226284 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) : term81 m n f g'.
Proof. exact (@lem7226283 m n f g'). Qed.
Lemma lem7226285 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) : (term81 m n f g') = (term82 m n f g').
Proof. exact (eq_refl (term81 m n f g')). Qed.
Lemma lem7226286 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) : term82 m n f g'.
Proof. exact (EQ_MP (@lem7226285 m n f g') (@lem7226284 m n f g')). Qed.
Lemma lem7226287 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) : term83 m n f g' t'.
Proof. exact (@lem7226286 m n f g' t'). Qed.
Lemma lem7226288 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) : (term83 m n f g' t') = (term84 m n f g' t').
Proof. exact (eq_refl (term83 m n f g' t')). Qed.
Lemma lem7226289 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) : term84 m n f g' t'.
Proof. exact (EQ_MP (@lem7226288 m n f g' t') (@lem7226287 m n f g' t')). Qed.
Lemma lem7226290 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term85 m n f g' t' e'.
Proof. exact (@lem7226289 m n f g' t' e'). Qed.
Lemma lem7226291 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : (term85 m n f g' t' e') = (term86 m n f g' t' e').
Proof. exact (eq_refl (term85 m n f g' t' e')). Qed.
Lemma lem7226292 (m : nat) (n : nat) (f : nat -> real) (g' : Prop) (t' : real) (e' : real) : term86 m n f g' t' e'.
Proof. exact (EQ_MP (@lem7226291 m n f g' t' e') (@lem7226290 m n f g' t' e')). Qed.
Lemma lem7226294 (m : nat) (n : nat) (h1 : term64 m n) : (term72 m n) = True.
Proof. exact (EQ_MP (@lem7226268 m n) (@lem7226267 m n h1)). Qed.
Lemma lem7226295 (m : nat) (n : nat) (f : nat -> real) (t' : real) (e' : real) : term87 m n f t' e'.
Proof. exact (@lem7226292 m n f True t' e'). Qed.
Lemma lem7226296 (f : nat -> real) (t' : real) (e' : real) (m : nat) (n : nat) (h1 : term64 m n) : term88 m n f t' e'.
Proof. exact (@lem7226295 m n f t' e' (@lem7226294 m n h1)). Qed.
Lemma lem7226302 (m : nat) (f : nat -> real) (n : nat) : (term79 m f n) = (term79 m f n).
Proof. exact (eq_refl (term79 m f n)). Qed.
Lemma lem7226303 (m : nat) (f : nat -> real) (n : nat) : term89 m f n.
Proof. exact (fun h0 : True => @lem7226302 m f n). Qed.
Lemma lem7226304 (f : nat -> real) (e' : real) (m : nat) (n : nat) (h1 : term64 m n) : term90 m f n e'.
Proof. exact (@lem7226296 f (term79 m f n) e' m n h1). Qed.
Lemma lem7226305 (f : nat -> real) (e' : real) (m : nat) (n : nat) (h1 : term64 m n) : term91 m f n e'.
Proof. exact (@lem7226304 f e' m n h1 (@lem7226303 m f n)). Qed.
Lemma lem7226309 (m : nat) (n : nat) (f : nat -> real) : (term80 m n f) = (term80 m n f).
Proof. exact (eq_refl (term80 m n f)). Qed.
Lemma lem7226310 (m : nat) (n : nat) (f : nat -> real) : term92 m n f.
Proof. exact (fun h0 : ~ True => @lem7226309 m n f). Qed.
Lemma lem7226311 (f : nat -> real) (m : nat) (n : nat) (h1 : term64 m n) : term93 m n f.
Proof. exact (@lem7226305 f (term80 m n f) m n h1). Qed.
Lemma lem7226312 (f : nat -> real) (m : nat) (n : nat) (h1 : term64 m n) : (term7 m n f) = (term94 m n f).
Proof. exact (@lem7226311 f m n h1 (@lem7226310 m n f)). Qed.
Lemma lem7226314 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7226315 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem7226314 real t2 t1). Qed.
Lemma lem7226316 (m : nat) (f : nat -> real) (n : nat) : (term94 m n f) = (term79 m f n).
Proof. exact (@lem7226315 (term80 m n f) (term79 m f n)). Qed.
Lemma lem7226317 (f : nat -> real) (m : nat) (n : nat) (h1 : term64 m n) : (term7 m n f) = (term79 m f n).
Proof. exact (TRANS (@lem7226312 f m n h1) (@lem7226316 m f n)). Qed.
Lemma lem7226318 (f : nat -> real) (m : nat) (n : nat) (h1 : term64 m n) : (term6 m n f) = (term79 m f n).
Proof. exact (TRANS (@lem7226276 m n f) (@lem7226317 f m n h1)). Qed.
Lemma lem7226319 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7226320 (f : nat -> real) (m : nat) (n : nat) (h1 : term64 m n) : (term95 m n f) = (term96 m f n).
Proof. exact (MK_COMB (@lem7226319) (@lem7226318 f m n h1)). Qed.
Lemma lem7226322 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem7226010 n) (@lem7226009 n)). Qed.
Lemma lem7226323 (m : nat) : (dotdot m) = (dotdot m).
Proof. exact (eq_refl (dotdot m)). Qed.
Lemma lem7226324 (m : nat) (n : nat) : (term97 m n) = (dotdot m n).
Proof. exact (MK_COMB (@lem7226323 m) (@lem7226322 n)). Qed.
Lemma lem7226325 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7226326 (m : nat) (n : nat) : (term98 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem7226325) (@lem7226324 m n)). Qed.
Lemma lem7226327 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7226328 (m : nat) (n : nat) (f : nat -> real) : (term100 m n f) = (term80 m n f).
Proof. exact (MK_COMB (@lem7226326 m n) (@lem7226327 f)). Qed.
Lemma lem7226329 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7226330 (m : nat) (n : nat) (f : nat -> real) : (term101 m n f) = (term102 m n f).
Proof. exact (MK_COMB (@lem7226329) (@lem7226328 m n f)). Qed.
Lemma lem7226331 (f : nat -> real) (n : nat) : (term103 f n) = (term103 f n).
Proof. exact (eq_refl (term103 f n)). Qed.
Lemma lem7226332 (m : nat) (f : nat -> real) (n : nat) : (term65 m f n) = (term79 m f n).
Proof. exact (MK_COMB (@lem7226330 m n f) (@lem7226331 f n)). Qed.
Lemma lem7226333 (f : nat -> real) (m : nat) (n : nat) (h1 : term64 m n) : ((term6 m n f) = (term65 m f n)) = ((term79 m f n) = (term79 m f n)).
Proof. exact (MK_COMB (@lem7226320 f m n h1) (@lem7226332 m f n)). Qed.
Lemma lem7226335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7226336 (x : real) : (x = x) = True.
Proof. exact (@lem7226335 real x). Qed.
Lemma lem7226337 (m : nat) (f : nat -> real) (n : nat) : ((term79 m f n) = (term79 m f n)) = True.
Proof. exact (@lem7226336 (term79 m f n)). Qed.
Lemma lem7226338 (f : nat -> real) (m : nat) (n : nat) (h1 : term64 m n) : ((term6 m n f) = (term65 m f n)) = True.
Proof. exact (TRANS (@lem7226333 f m n h1) (@lem7226337 m f n)). Qed.
Lemma lem7226339 (m : nat) (f : nat -> real) (n : nat) : term104 m f n.
Proof. exact (fun h0 : term64 m n => @lem7226338 f m n h0). Qed.
Lemma lem7226340 (f : nat -> real) (m : nat) (n : nat) : term105 f m n.
Proof. exact (@lem7226265 f m n True). Qed.
Lemma lem7226341 (f : nat -> real) (m : nat) (n : nat) : (term27 m f n) = (term106 m n).
Proof. exact (@lem7226340 f m n (@lem7226339 m f n)). Qed.
Lemma lem7226343 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7226344 (m : nat) (n : nat) : (term106 m n) = True.
Proof. exact (@lem7226343 (term64 m n)). Qed.
Lemma lem7226345 (m : nat) (f : nat -> real) (n : nat) : (term27 m f n) = True.
Proof. exact (TRANS (@lem7226341 f m n) (@lem7226344 m n)). Qed.
Lemma lem7226346 (m : nat) (f : nat -> real) (n : nat) : True = (term27 m f n).
Proof. exact (SYM (@lem7226345 m f n)). Qed.
Lemma lem7226347 (m : nat) (f : nat -> real) (n : nat) : term27 m f n.
Proof. exact (EQ_MP (@lem7226346 m f n) (@lem0)). Qed.
Lemma lem7226348 (m : nat) (f : nat -> real) (n : nat) : term29 m f n.
Proof. exact (fun h0 : term23 m f n => @lem7226347 m f n). Qed.
Lemma lem7226353 (m : nat) (f : nat -> real) : term33 m f.
Proof. exact (fun n : nat => @lem7226348 m f n). Qed.
Lemma lem7226354 (m : nat) (f : nat -> real) : term35 m f.
Proof. exact (conj (@lem7226245 m f) (@lem7226353 m f)). Qed.
Lemma lem7226355 (m : nat) (f : nat -> real) : term40 m f.
Proof. exact (@lem7226050 m f (@lem7226354 m f)). Qed.
Lemma lem7226360 (f : nat -> real) : term107 f.
Proof. exact (fun m : nat => @lem7226355 m f). Qed.
Lemma lem7226365 : term108.
Proof. exact (fun f : nat -> real => @lem7226360 f). Qed.
