Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_GENERAL_INVERSES_term_abbrevs.
Require Import ITERATE_EQ_GENERAL_INVERSES_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7018206 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7018208 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7018209 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7018208 A B C h1 op). Qed.
Lemma lem7018210 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7018211 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7018210 A B C op) (@lem7018209 A B C op h1)). Qed.
Lemma lem7018212 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7018213 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7018211 A B C op h1 (@lem7018212 C op h2)). Qed.
Lemma lem7018214 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7018213 A B C op h0 h1). Qed.
Lemma lem7018215 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7018216 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7018214 A B C op h2 (@lem7018215 A B C h1)). Qed.
Lemma lem7018217 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7018216 A B C op h1 h0). Qed.
Lemma lem7018218 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7018217 A B C op h1). Qed.
Lemma lem7018219 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7018218 A B C h0). Qed.
Lemma lem7018220 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7018219 A B C (@lem6000071 A B C)). Qed.
Lemma lem7018221 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7018220 A B C op). Qed.
Lemma lem7018222 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7018279 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018280 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7018279 A). Qed.
Lemma lem7018281 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7018282 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem7018280 A) (@lem7018281 A s)). Qed.
Lemma lem7018283 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018284 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@iterate nat A Nat.add s f).
Proof. exact (MK_COMB (@lem7018282 A s) (@lem7018283 A f)). Qed.
Lemma lem7018285 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7018286 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7018285) (@lem7018284 A s f)). Qed.
Lemma lem7018288 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018289 {B : Type'} : (@nsum B) = (@iterate nat B Nat.add).
Proof. exact (@lem7018288 B). Qed.
Lemma lem7018290 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7018291 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@iterate nat B Nat.add t).
Proof. exact (MK_COMB (@lem7018289 B) (@lem7018290 B t)). Qed.
Lemma lem7018292 {B : Type'} (g : B -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7018293 {B : Type'} (t : B -> Prop) (g : B -> nat) : (@nsum B t g) = (@iterate nat B Nat.add t g).
Proof. exact (MK_COMB (@lem7018291 B t) (@lem7018292 B g)). Qed.
Lemma lem7018294 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : ((@nsum A s f) = (@nsum B t g)) = ((@iterate nat A Nat.add s f) = (@iterate nat B Nat.add t g)).
Proof. exact (MK_COMB (@lem7018286 A s f) (@lem7018293 B t g)). Qed.
Lemma lem7018297 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (k : B -> A) (g : B -> nat) (h : A -> B) (f : A -> nat) : (term8 A B s t k g h f) = (term8 A B s t k g h f).
Proof. exact (eq_refl (term8 A B s t k g h f)). Qed.
Lemma lem7018298 {A B : Type'} (k : B -> A) (h : A -> B) (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term9 A B k h s f t g) = (term10 A B k h s f t g).
Proof. exact (MK_COMB (@lem7018297 A B s t k g h f) (@lem7018294 A B s f t g)). Qed.
Lemma lem7018301 {A B : Type'} (h : A -> B) (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term11 A B h s f t g) = (term12 A B h s f t g).
Proof. exact (fun_ext (fun k : B -> A => @lem7018298 A B k h s f t g)). Qed.
Lemma lem7018302 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem7018303 {A B : Type'} (h : A -> B) (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term13 A B h s f t g) = (term14 A B h s f t g).
Proof. exact (MK_COMB (@lem7018302 A B) (@lem7018301 A B h s f t g)). Qed.
Lemma lem7018308 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term15 A B s f t g) = (term16 A B s f t g).
Proof. exact (fun_ext (fun h : A -> B => @lem7018303 A B h s f t g)). Qed.
Lemma lem7018309 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7018310 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term17 A B s f t g) = (term18 A B s f t g).
Proof. exact (MK_COMB (@lem7018309 A B) (@lem7018308 A B s f t g)). Qed.
Lemma lem7018315 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) : (term19 A B s f t) = (term20 A B s f t).
Proof. exact (fun_ext (fun g : B -> nat => @lem7018310 A B s f t g)). Qed.
Lemma lem7018316 {B : Type'} : (@all (B -> nat)) = (@all (B -> nat)).
Proof. exact (eq_refl (@all (B -> nat))). Qed.
Lemma lem7018317 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) : (term21 A B s f t) = (term22 A B s f t).
Proof. exact (MK_COMB (@lem7018316 B) (@lem7018315 A B s f t)). Qed.
Lemma lem7018322 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term23 A B s t) = (term24 A B s t).
Proof. exact (fun_ext (fun f : A -> nat => @lem7018317 A B s f t)). Qed.
Lemma lem7018323 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7018324 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term25 A B s t) = (term26 A B s t).
Proof. exact (MK_COMB (@lem7018323 A) (@lem7018322 A B s t)). Qed.
Lemma lem7018329 {A B : Type'} (s : A -> Prop) : (term27 A B s) = (term28 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7018324 A B s t)). Qed.
Lemma lem7018330 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7018331 {A B : Type'} (s : A -> Prop) : (term29 A B s) = (term30 A B s).
Proof. exact (MK_COMB (@lem7018330 B) (@lem7018329 A B s)). Qed.
Lemma lem7018336 {A B : Type'} : (term31 A B) = (term32 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7018331 A B s)). Qed.
Lemma lem7018337 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7018338 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7018337 A) (@lem7018336 A B)). Qed.
Lemma lem7018343 {A B : Type'} : (term34 A B) = (term33 A B).
Proof. exact (SYM (@lem7018338 A B)). Qed.
Lemma lem7018345 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7018222 A B C op) (@lem7018221 A B C op)). Qed.
Lemma lem7018346 {A B : Type'} (op : type1606) : term35 A B op.
Proof. exact (@lem7018345 A B nat op). Qed.
Lemma lem7018347 {A B : Type'} : term36 A B.
Proof. exact (@lem7018346 A B Nat.add). Qed.
Lemma lem7018349 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7018206) (@lem6924403)). Qed.
Lemma lem7018350 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7018349)). Qed.
Lemma lem7018351 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7018350) (@lem0)). Qed.
Lemma lem7018352 {A B : Type'} : term34 A B.
Proof. exact (@lem7018347 A B (@lem7018351)). Qed.
Lemma lem7018353 {A B : Type'} : term33 A B.
Proof. exact (EQ_MP (@lem7018343 A B) (@lem7018352 A B)). Qed.
