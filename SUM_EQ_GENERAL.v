Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_EQ_GENERAL_term_abbrevs.
Require Import ITERATE_EQ_GENERAL_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7178268 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7178270 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7178271 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7178270 A B C h1 op). Qed.
Lemma lem7178272 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7178273 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7178272 A B C op) (@lem7178271 A B C op h1)). Qed.
Lemma lem7178274 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7178275 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7178273 A B C op h1 (@lem7178274 C op h2)). Qed.
Lemma lem7178276 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7178275 A B C op h0 h1). Qed.
Lemma lem7178277 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7178278 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7178276 A B C op h2 (@lem7178277 A B C h1)). Qed.
Lemma lem7178279 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7178278 A B C op h1 h0). Qed.
Lemma lem7178280 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7178279 A B C op h1). Qed.
Lemma lem7178281 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7178280 A B C h0). Qed.
Lemma lem7178282 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7178281 A B C (@lem5997003 A B C)). Qed.
Lemma lem7178283 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7178282 A B C op). Qed.
Lemma lem7178284 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7178333 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178334 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7178333 A). Qed.
Lemma lem7178335 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178336 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7178334 A) (@lem7178335 A s)). Qed.
Lemma lem7178337 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178338 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@iterate real A real_add s f).
Proof. exact (MK_COMB (@lem7178336 A s) (@lem7178337 A f)). Qed.
Lemma lem7178339 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7178340 {A : Type'} (s : A -> Prop) (f : A -> real) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7178339) (@lem7178338 A s f)). Qed.
Lemma lem7178342 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178343 {B : Type'} : (@sum B) = (@iterate real B real_add).
Proof. exact (@lem7178342 B). Qed.
Lemma lem7178344 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7178345 {B : Type'} (t : B -> Prop) : (@sum B t) = (@iterate real B real_add t).
Proof. exact (MK_COMB (@lem7178343 B) (@lem7178344 B t)). Qed.
Lemma lem7178346 {B : Type'} (g : B -> real) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7178347 {B : Type'} (t : B -> Prop) (g : B -> real) : (@sum B t g) = (@iterate real B real_add t g).
Proof. exact (MK_COMB (@lem7178345 B t) (@lem7178346 B g)). Qed.
Lemma lem7178348 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : ((@sum A s f) = (@sum B t g)) = ((@iterate real A real_add s f) = (@iterate real B real_add t g)).
Proof. exact (MK_COMB (@lem7178340 A s f) (@lem7178347 B t g)). Qed.
Lemma lem7178351 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> real) (h : A -> B) (f : A -> real) : (term8 A B s t g h f) = (term8 A B s t g h f).
Proof. exact (eq_refl (term8 A B s t g h f)). Qed.
Lemma lem7178352 {A B : Type'} (h : A -> B) (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term9 A B h s f t g) = (term10 A B h s f t g).
Proof. exact (MK_COMB (@lem7178351 A B s t g h f) (@lem7178348 A B s f t g)). Qed.
Lemma lem7178355 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term11 A B s f t g) = (term12 A B s f t g).
Proof. exact (fun_ext (fun h : A -> B => @lem7178352 A B h s f t g)). Qed.
Lemma lem7178356 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7178357 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) (g : B -> real) : (term13 A B s f t g) = (term14 A B s f t g).
Proof. exact (MK_COMB (@lem7178356 A B) (@lem7178355 A B s f t g)). Qed.
Lemma lem7178362 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) : (term15 A B s f t) = (term16 A B s f t).
Proof. exact (fun_ext (fun g : B -> real => @lem7178357 A B s f t g)). Qed.
Lemma lem7178363 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7178364 {A B : Type'} (s : A -> Prop) (f : A -> real) (t : B -> Prop) : (term17 A B s f t) = (term18 A B s f t).
Proof. exact (MK_COMB (@lem7178363 B) (@lem7178362 A B s f t)). Qed.
Lemma lem7178369 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term19 A B s t) = (term20 A B s t).
Proof. exact (fun_ext (fun f : A -> real => @lem7178364 A B s f t)). Qed.
Lemma lem7178370 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7178371 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term21 A B s t) = (term22 A B s t).
Proof. exact (MK_COMB (@lem7178370 A) (@lem7178369 A B s t)). Qed.
Lemma lem7178376 {A B : Type'} (s : A -> Prop) : (term23 A B s) = (term24 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7178371 A B s t)). Qed.
Lemma lem7178377 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7178378 {A B : Type'} (s : A -> Prop) : (term25 A B s) = (term26 A B s).
Proof. exact (MK_COMB (@lem7178377 B) (@lem7178376 A B s)). Qed.
Lemma lem7178383 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7178378 A B s)). Qed.
Lemma lem7178384 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7178385 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem7178384 A) (@lem7178383 A B)). Qed.
Lemma lem7178390 {A B : Type'} : (term30 A B) = (term29 A B).
Proof. exact (SYM (@lem7178385 A B)). Qed.
Lemma lem7178392 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7178284 A B C op) (@lem7178283 A B C op)). Qed.
Lemma lem7178393 {A B : Type'} (op : type1627) : term31 A B op.
Proof. exact (@lem7178392 A B real op). Qed.
Lemma lem7178394 {A B : Type'} : term32 A B.
Proof. exact (@lem7178393 A B real_add). Qed.
Lemma lem7178396 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7178268) (@lem7067132)). Qed.
Lemma lem7178397 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7178396)). Qed.
Lemma lem7178398 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7178397) (@lem0)). Qed.
Lemma lem7178399 {A B : Type'} : term30 A B.
Proof. exact (@lem7178394 A B (@lem7178398)). Qed.
Lemma lem7178400 {A B : Type'} : term29 A B.
Proof. exact (EQ_MP (@lem7178390 A B) (@lem7178399 A B)). Qed.
