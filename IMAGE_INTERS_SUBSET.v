Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_INTERS_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INTERS_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm18394_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3486252 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term0 _89465 _89481 f.
Proof. exact (@lem3453847 _89465 _89481 f). Qed.
Lemma lem3486253 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term0 _89465 _89481 f) = (term1 _89465 _89481 f).
Proof. exact (eq_refl (term0 _89465 _89481 f)). Qed.
Lemma lem3486254 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term1 _89465 _89481 f.
Proof. exact (EQ_MP (@lem3486253 _89465 _89481 f) (@lem3486252 _89465 _89481 f)). Qed.
Lemma lem3486255 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) : term2 _89465 _89481 f s.
Proof. exact (@lem3486254 _89465 _89481 f s). Qed.
Lemma lem3486256 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term2 _89465 _89481 f s) = ((term3 _89465 _89481 f s) = (term4 _89465 _89481 s f)).
Proof. exact (eq_refl (term2 _89465 _89481 f s)). Qed.
Lemma lem3486267 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term3 _89465 _89481 f s) = (term4 _89465 _89481 s f).
Proof. exact (EQ_MP (@lem3486256 _89465 _89481 s f) (@lem3486255 _89465 _89481 f s)). Qed.
Lemma lem3486268 {A B : Type'} (s : type686 A) (f : type678 A B) : (term5 A B f s) = (term6 A B s f).
Proof. exact (@lem3486267 B (A -> Prop) s f). Qed.
Lemma lem3486269 {A B : Type'} (g : type686 A) (f : A -> B) : (term7 A B f g) = (term8 A B g f).
Proof. exact (@lem3486268 A B g (@IMAGE A B f)). Qed.
Lemma lem3486280 {A B : Type'} (f : A -> B) (g : type686 A) : (term9 A B f g) = (term9 A B f g).
Proof. exact (eq_refl (term9 A B f g)). Qed.
Lemma lem3486281 {A B : Type'} (g : type686 A) (f : A -> B) : (term10 A B f g) = (term11 A B g f).
Proof. exact (MK_COMB (@lem3486280 A B f g) (@lem3486269 A B g f)). Qed.
Lemma lem3486282 {A B : Type'} (f : A -> B) : (term12 A B f) = (term13 A B f).
Proof. exact (fun_ext (fun g : type686 A => @lem3486281 A B g f)). Qed.
Lemma lem3486283 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3486284 {A B : Type'} (f : A -> B) : (term14 A B f) = (term15 A B f).
Proof. exact (MK_COMB (@lem3486283 A) (@lem3486282 A B f)). Qed.
Lemma lem3486289 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3486284 A B f)). Qed.
Lemma lem3486290 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3486291 {A B : Type'} : (term18 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem3486290 A B) (@lem3486289 A B)). Qed.
Lemma lem3486296 {A B : Type'} : (term19 A B) = (term18 A B).
Proof. exact (SYM (@lem3486291 A B)). Qed.
Lemma lem3486306 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3486307 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term20 B s t).
Proof. exact (@lem3486306 B s t). Qed.
Lemma lem3486308 {A B : Type'} (g : type686 A) (f : A -> B) : (term11 A B g f) = (term21 A B g f).
Proof. exact (@lem3486307 B (term22 A B f g) (term8 A B g f)). Qed.
Lemma lem3486325 {A B : Type'} (f : A -> B) : (term13 A B f) = (term23 A B f).
Proof. exact (fun_ext (fun g : type686 A => @lem3486308 A B g f)). Qed.
Lemma lem3486326 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3486327 {A B : Type'} (f : A -> B) : (term15 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem3486326 A) (@lem3486325 A B f)). Qed.
Lemma lem3486332 {A B : Type'} : (term17 A B) = (term25 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3486327 A B f)). Qed.
Lemma lem3486333 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3486334 {A B : Type'} : (term19 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem3486333 A B) (@lem3486332 A B)). Qed.
Lemma lem3486339 {A B : Type'} : (term26 A B) = (term19 A B).
Proof. exact (SYM (@lem3486334 A B)). Qed.
Lemma lem3486355 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term27 A B y f s) = (term28 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3486356 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term27 A B y f s) = (term28 A B y f s).
Proof. exact (@lem3486355 A B y f s). Qed.
Lemma lem3486357 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term29 A B x f g) = (term30 A B x f g).
Proof. exact (@lem3486356 A B x f (@INTERS A g)). Qed.
Lemma lem3486367 {A : Type'} (s : type686 A) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3486368 {A : Type'} (s : type686 A) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (@lem3486367 A s x). Qed.
Lemma lem3486369 {A : Type'} (g : type686 A) (x : A) : (term31 A x g) = (term32 A g x).
Proof. exact (@lem3486368 A g x). Qed.
Lemma lem3486377 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3486378 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3486377 (A -> Prop) P x). Qed.
Lemma lem3486379 {A : Type'} (g : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t g) = (g t).
Proof. exact (@lem3486378 A g t). Qed.
Lemma lem3486380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3486381 {A : Type'} (g : type686 A) (t : A -> Prop) : (term33 A t g) = (term34 A g t).
Proof. exact (MK_COMB (@lem3486380) (@lem3486379 A g t)). Qed.
Lemma lem3486383 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3486384 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3486383 A P x). Qed.
Lemma lem3486385 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3486384 A t x). Qed.
Lemma lem3486386 {A : Type'} (g : type686 A) (t : A -> Prop) (x : A) : (term35 A g x t) = (term36 A g t x).
Proof. exact (MK_COMB (@lem3486381 A g t) (@lem3486385 A t x)). Qed.
Lemma lem3486389 {A : Type'} (g : type686 A) (x : A) : (term37 A g x) = (term38 A g x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3486386 A g t x)). Qed.
Lemma lem3486390 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3486391 {A : Type'} (g : type686 A) (x : A) : (term32 A g x) = (term39 A g x).
Proof. exact (MK_COMB (@lem3486390 A) (@lem3486389 A g x)). Qed.
Lemma lem3486396 {A : Type'} (g : type686 A) (x : A) : (term31 A x g) = (term39 A g x).
Proof. exact (TRANS (@lem3486369 A g x) (@lem3486391 A g x)). Qed.
Lemma lem3486397 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term40 A B x f x') = (term40 A B x f x').
Proof. exact (eq_refl (term40 A B x f x')). Qed.
Lemma lem3486398 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A) : (term41 A B x f x' g) = (term42 A B x f g x').
Proof. exact (MK_COMB (@lem3486397 A B x f x') (@lem3486396 A g x')). Qed.
Lemma lem3486401 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term43 A B x f g) = (term44 A B x f g).
Proof. exact (fun_ext (fun x' : A => @lem3486398 A B x f g x')). Qed.
Lemma lem3486402 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3486403 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term30 A B x f g) = (term45 A B x f g).
Proof. exact (MK_COMB (@lem3486402 A) (@lem3486401 A B x f g)). Qed.
Lemma lem3486408 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term29 A B x f g) = (term45 A B x f g).
Proof. exact (TRANS (@lem3486357 A B x f g) (@lem3486403 A B x f g)). Qed.
Lemma lem3486409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3486410 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term46 A B x f g) = (term47 A B x f g).
Proof. exact (MK_COMB (@lem3486409) (@lem3486408 A B x f g)). Qed.
Lemma lem3486412 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term48 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3486413 {B : Type'} (p : B -> Prop) (x : B) : (term48 B x p) = (p x).
Proof. exact (@lem3486412 B p x). Qed.
Lemma lem3486414 {A B : Type'} (g : type686 A) (f : A -> B) (x : B) : (term49 A B x g f) = (term50 A B g f x).
Proof. exact (@lem3486413 B (term51 A B g f) x). Qed.
Lemma lem3486415 {A B : Type'} (g : type686 A) (y : B) (f : A -> B) : (term50 A B g f y) = (term52 A B g y f).
Proof. exact (eq_refl (term50 A B g f y)). Qed.
Lemma lem3486416 {B : Type'} (GEN_PVAR_48 : B) : (@SETSPEC B GEN_PVAR_48) = (@SETSPEC B GEN_PVAR_48).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_48)). Qed.
Lemma lem3486417 {A B : Type'} (GEN_PVAR_48 : B) (g : type686 A) (y : B) (f : A -> B) : (term53 A B GEN_PVAR_48 g f y) = (term54 A B GEN_PVAR_48 g y f).
Proof. exact (MK_COMB (@lem3486416 B GEN_PVAR_48) (@lem3486415 A B g y f)). Qed.
Lemma lem3486418 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3486419 {A B : Type'} (GEN_PVAR_48 : B) (g : type686 A) (f : A -> B) (y : B) : (term55 A B GEN_PVAR_48 g f y) = (term56 A B GEN_PVAR_48 g f y).
Proof. exact (MK_COMB (@lem3486417 A B GEN_PVAR_48 g y f) (@lem3486418 B y)). Qed.
Lemma lem3486420 {A B : Type'} (GEN_PVAR_48 : B) (g : type686 A) (f : A -> B) : (term57 A B GEN_PVAR_48 g f) = (term58 A B GEN_PVAR_48 g f).
Proof. exact (fun_ext (fun y : B => @lem3486419 A B GEN_PVAR_48 g f y)). Qed.
Lemma lem3486421 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3486422 {A B : Type'} (GEN_PVAR_48 : B) (g : type686 A) (f : A -> B) : (term59 A B GEN_PVAR_48 g f) = (term60 A B GEN_PVAR_48 g f).
Proof. exact (MK_COMB (@lem3486421 B) (@lem3486420 A B GEN_PVAR_48 g f)). Qed.
Lemma lem3486423 {A B : Type'} (g : type686 A) (f : A -> B) : (term61 A B g f) = (term62 A B g f).
Proof. exact (fun_ext (fun GEN_PVAR_48 : B => @lem3486422 A B GEN_PVAR_48 g f)). Qed.
Lemma lem3486424 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3486425 {A B : Type'} (g : type686 A) (f : A -> B) : (term63 A B g f) = (term8 A B g f).
Proof. exact (MK_COMB (@lem3486424 B) (@lem3486423 A B g f)). Qed.
Lemma lem3486426 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3486427 {A B : Type'} (x : B) (g : type686 A) (f : A -> B) : (term49 A B x g f) = (term64 A B x g f).
Proof. exact (MK_COMB (@lem3486426 B x) (@lem3486425 A B g f)). Qed.
Lemma lem3486428 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3486429 {A B : Type'} (x : B) (g : type686 A) (f : A -> B) : (term65 A B x g f) = (term66 A B x g f).
Proof. exact (MK_COMB (@lem3486428) (@lem3486427 A B x g f)). Qed.
Lemma lem3486430 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term50 A B g f x) = (term52 A B g x f).
Proof. exact (eq_refl (term50 A B g f x)). Qed.
Lemma lem3486431 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : ((term49 A B x g f) = (term50 A B g f x)) = ((term64 A B x g f) = (term52 A B g x f)).
Proof. exact (MK_COMB (@lem3486429 A B x g f) (@lem3486430 A B g x f)). Qed.
Lemma lem3486432 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term64 A B x g f) = (term52 A B g x f).
Proof. exact (EQ_MP (@lem3486431 A B g x f) (@lem3486414 A B g f x)). Qed.
Lemma lem3486440 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3486441 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3486440 (A -> Prop) P x). Qed.
Lemma lem3486442 {A : Type'} (g : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x g) = (g x).
Proof. exact (@lem3486441 A g x). Qed.
Lemma lem3486443 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3486444 {A : Type'} (g : type686 A) (x : A -> Prop) : (term33 A x g) = (term34 A g x).
Proof. exact (MK_COMB (@lem3486443) (@lem3486442 A g x)). Qed.
Lemma lem3486446 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term27 A B y f s) = (term28 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3486447 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term27 A B y f s) = (term28 A B y f s).
Proof. exact (@lem3486446 A B y f s). Qed.
Lemma lem3486448 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term27 A B x f x') = (term28 A B x f x').
Proof. exact (@lem3486447 A B x f x'). Qed.
Lemma lem3486458 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3486459 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3486458 A P x). Qed.
Lemma lem3486460 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem3486459 A x x'). Qed.
Lemma lem3486461 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term40 A B x f x') = (term40 A B x f x').
Proof. exact (eq_refl (term40 A B x f x')). Qed.
Lemma lem3486462 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term67 A B x f x'' x') = (term68 A B x f x' x'').
Proof. exact (MK_COMB (@lem3486461 A B x f x'') (@lem3486460 A x' x'')). Qed.
Lemma lem3486465 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term69 A B x f x') = (term70 A B x f x').
Proof. exact (fun_ext (fun x'' : A => @lem3486462 A B x f x' x'')). Qed.
Lemma lem3486466 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3486467 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term28 A B x f x') = (term71 A B x f x').
Proof. exact (MK_COMB (@lem3486466 A) (@lem3486465 A B x f x')). Qed.
Lemma lem3486472 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term27 A B x f x') = (term71 A B x f x').
Proof. exact (TRANS (@lem3486448 A B x f x') (@lem3486467 A B x f x')). Qed.
Lemma lem3486473 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) (x' : A -> Prop) : (term72 A B g x f x') = (term73 A B g x f x').
Proof. exact (MK_COMB (@lem3486444 A g x') (@lem3486472 A B x f x')). Qed.
Lemma lem3486476 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term74 A B g x f) = (term75 A B g x f).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3486473 A B g x f x')). Qed.
Lemma lem3486477 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3486478 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term52 A B g x f) = (term76 A B g x f).
Proof. exact (MK_COMB (@lem3486477 A) (@lem3486476 A B g x f)). Qed.
Lemma lem3486483 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term64 A B x g f) = (term76 A B g x f).
Proof. exact (TRANS (@lem3486432 A B g x f) (@lem3486478 A B g x f)). Qed.
Lemma lem3486484 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term77 A B x g f) = (term78 A B g x f).
Proof. exact (MK_COMB (@lem3486410 A B x f g) (@lem3486483 A B g x f)). Qed.
Lemma lem3486487 {A B : Type'} (g : type686 A) (f : A -> B) : (term79 A B g f) = (term80 A B g f).
Proof. exact (fun_ext (fun x : B => @lem3486484 A B g x f)). Qed.
Lemma lem3486488 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3486489 {A B : Type'} (g : type686 A) (f : A -> B) : (term21 A B g f) = (term81 A B g f).
Proof. exact (MK_COMB (@lem3486488 B) (@lem3486487 A B g f)). Qed.
Lemma lem3486494 {A B : Type'} (f : A -> B) : (term23 A B f) = (term82 A B f).
Proof. exact (fun_ext (fun g : type686 A => @lem3486489 A B g f)). Qed.
Lemma lem3486495 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3486496 {A B : Type'} (f : A -> B) : (term24 A B f) = (term83 A B f).
Proof. exact (MK_COMB (@lem3486495 A) (@lem3486494 A B f)). Qed.
Lemma lem3486501 {A B : Type'} : (term25 A B) = (term84 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3486496 A B f)). Qed.
Lemma lem3486502 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3486503 {A B : Type'} : (term26 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem3486502 A B) (@lem3486501 A B)). Qed.
Lemma lem3486508 {A B : Type'} : (term85 A B) = (term26 A B).
Proof. exact (SYM (@lem3486503 A B)). Qed.
Lemma lem3486510 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3486511 {A B : Type'} : (term85 A B) = (term87 A B).
Proof. exact (@lem3486510 (term85 A B)). Qed.
Lemma lem3486512 {A B : Type'} : (term87 A B) = (term85 A B).
Proof. exact (SYM (@lem3486511 A B)). Qed.
Lemma lem3486513 {A B : Type'} (h1 : term88 A B) : term88 A B.
Proof. exact (h1). Qed.
Lemma lem3486516 {A B : Type'} (h1 : term87 A B) : term87 A B.
Proof. exact (h1). Qed.
Lemma lem3486517 {A B : Type'} : term89 A B.
Proof. exact (fun h0 : term87 A B => @lem3486516 A B h0). Qed.
Lemma lem3486518 {A B : Type'} (h1 : term89 A B) : term89 A B.
Proof. exact (h1). Qed.
Lemma lem3486519 {A B : Type'} (h1 : term87 A B) : term87 A B.
Proof. exact (h1). Qed.
Lemma lem3486520 {A B : Type'} (h1 : term87 A B) (h2 : term89 A B) : term87 A B.
Proof. exact (@lem3486518 A B h2 (@lem3486519 A B h1)). Qed.
Lemma lem3486521 {A B : Type'} (h1 : term87 A B) : term90 A B.
Proof. exact (fun h0 : term89 A B => @lem3486520 A B h1 h0). Qed.
Lemma lem3486522 {A B : Type'} (h1 : term89 A B) : term89 A B.
Proof. exact (h1). Qed.
Lemma lem3486523 {A B : Type'} (h1 : term87 A B) (h2 : term89 A B) : term87 A B.
Proof. exact (@lem3486521 A B h1 (@lem3486522 A B h2)). Qed.
Lemma lem3486524 {A B : Type'} (h1 : term89 A B) : term89 A B.
Proof. exact (fun h0 : term87 A B => @lem3486523 A B h0 h1). Qed.
Lemma lem3486525 {A B : Type'} : term91 A B.
Proof. exact (fun h0 : term89 A B => @lem3486524 A B h0). Qed.
Lemma lem3486528 {A B : Type'} : term89 A B.
Proof. exact (@lem3486525 A B (@lem3486517 A B)). Qed.
Lemma lem3486529 {A B : Type'} : term89 A B.
Proof. exact (@lem3486528 A B). Qed.
Lemma lem3486531 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3486532 {A B : Type'} : (term87 A B) = (term92 A B).
Proof. exact (@lem3486531 (term88 A B)). Qed.
Lemma lem3486534 (t : Prop) : (term93 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3486535 {A B : Type'} : (term92 A B) = (term85 A B).
Proof. exact (@lem3486534 (term85 A B)). Qed.
Lemma lem3486650 {A B : Type'} : (term87 A B) = (term85 A B).
Proof. exact (TRANS (@lem3486532 A B) (@lem3486535 A B)). Qed.
Lemma lem3486655 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term68 A B x f x' x'') = (term68 A B x f x' x'').
Proof. exact (eq_refl (term68 A B x f x' x'')). Qed.
Lemma lem3486656 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term70 A B x f x') = (term70 A B x f x').
Proof. exact (fun_ext (fun x'' : A => @lem3486655 A B x f x' x'')). Qed.
Lemma lem3486657 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3486658 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term71 A B x f x') = (term71 A B x f x').
Proof. exact (MK_COMB (@lem3486657 A) (@lem3486656 A B x f x')). Qed.
Lemma lem3486661 {A : Type'} (g : type686 A) (x : A -> Prop) : (term34 A g x) = (term34 A g x).
Proof. exact (eq_refl (term34 A g x)). Qed.
Lemma lem3486662 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) (x' : A -> Prop) : (term73 A B g x f x') = (term73 A B g x f x').
Proof. exact (MK_COMB (@lem3486661 A g x') (@lem3486658 A B x f x')). Qed.
Lemma lem3486663 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term75 A B g x f) = (term75 A B g x f).
Proof. exact (fun_ext (fun x' : A -> Prop => @lem3486662 A B g x f x')). Qed.
Lemma lem3486664 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3486665 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term76 A B g x f) = (term76 A B g x f).
Proof. exact (MK_COMB (@lem3486664 A) (@lem3486663 A B g x f)). Qed.
Lemma lem3486670 {A : Type'} (g : type686 A) (t : A -> Prop) (x : A) : (term36 A g t x) = (term36 A g t x).
Proof. exact (eq_refl (term36 A g t x)). Qed.
Lemma lem3486671 {A : Type'} (g : type686 A) (x : A) : (term38 A g x) = (term38 A g x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3486670 A g t x)). Qed.
Lemma lem3486672 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3486673 {A : Type'} (g : type686 A) (x : A) : (term39 A g x) = (term39 A g x).
Proof. exact (MK_COMB (@lem3486672 A) (@lem3486671 A g x)). Qed.
Lemma lem3486676 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term40 A B x f x') = (term40 A B x f x').
Proof. exact (eq_refl (term40 A B x f x')). Qed.
Lemma lem3486677 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A) : (term42 A B x f g x') = (term42 A B x f g x').
Proof. exact (MK_COMB (@lem3486676 A B x f x') (@lem3486673 A g x')). Qed.
Lemma lem3486678 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term44 A B x f g) = (term44 A B x f g).
Proof. exact (fun_ext (fun x' : A => @lem3486677 A B x f g x')). Qed.
Lemma lem3486679 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3486680 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term45 A B x f g) = (term45 A B x f g).
Proof. exact (MK_COMB (@lem3486679 A) (@lem3486678 A B x f g)). Qed.
Lemma lem3486681 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3486682 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term47 A B x f g) = (term47 A B x f g).
Proof. exact (MK_COMB (@lem3486681) (@lem3486680 A B x f g)). Qed.
Lemma lem3486683 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : (term78 A B g x f) = (term78 A B g x f).
Proof. exact (MK_COMB (@lem3486682 A B x f g) (@lem3486665 A B g x f)). Qed.
Lemma lem3486684 {A B : Type'} (g : type686 A) (f : A -> B) : (term80 A B g f) = (term80 A B g f).
Proof. exact (fun_ext (fun x : B => @lem3486683 A B g x f)). Qed.
Lemma lem3486685 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3486686 {A B : Type'} (g : type686 A) (f : A -> B) : (term81 A B g f) = (term81 A B g f).
Proof. exact (MK_COMB (@lem3486685 B) (@lem3486684 A B g f)). Qed.
Lemma lem3486687 {A B : Type'} (f : A -> B) : (term82 A B f) = (term82 A B f).
Proof. exact (fun_ext (fun g : type686 A => @lem3486686 A B g f)). Qed.
Lemma lem3486688 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3486689 {A B : Type'} (f : A -> B) : (term83 A B f) = (term83 A B f).
Proof. exact (MK_COMB (@lem3486688 A) (@lem3486687 A B f)). Qed.
Lemma lem3486690 {A B : Type'} : (term84 A B) = (term84 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3486689 A B f)). Qed.
Lemma lem3486691 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3486692 {A B : Type'} : (term85 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem3486691 A B) (@lem3486690 A B)). Qed.
Lemma lem3486747 {A B : Type'} : (term87 A B) = (term85 A B).
Proof. exact (TRANS (@lem3486650 A B) (@lem3486692 A B)). Qed.
Lemma lem3486748 {A B : Type'} : (term85 A B) = (term87 A B).
Proof. exact (SYM (@lem3486747 A B)). Qed.
Lemma lem3486749 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (h1 : term45 A B x f g) : term45 A B x f g.
Proof. exact (h1). Qed.
Lemma lem3486752 (p : Prop) : p = (term86 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3486753 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term71 A B x f x') = (term94 A B x f x').
Proof. exact (@lem3486752 (term71 A B x f x')). Qed.
Lemma lem3486754 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term94 A B x f x') = (term71 A B x f x').
Proof. exact (SYM (@lem3486753 A B x f x')). Qed.
Lemma lem3486755 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (h1 : term95 A B x f x') : term95 A B x f x'.
Proof. exact (h1). Qed.
Lemma lem3486763 {A : Type'} (g : type686 A) (t : A -> Prop) (x : A) : (term36 A g t x) = (term96 A g t x).
Proof. exact (@lem17265 (g t) (t x)). Qed.
Lemma lem3486764 {A : Type'} (g : type686 A) (x : A) : (term38 A g x) = (term97 A g x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3486763 A g t x)). Qed.
Lemma lem3486765 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3486766 {A : Type'} (g : type686 A) (x : A) : (term39 A g x) = (term98 A g x).
Proof. exact (MK_COMB (@lem3486765 A) (@lem3486764 A g x)). Qed.
Lemma lem3486768 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term40 A B x f x') = (term40 A B x f x').
Proof. exact (eq_refl (term40 A B x f x')). Qed.
Lemma lem3486769 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A) : (term42 A B x f g x') = (term99 A B x f g x').
Proof. exact (MK_COMB (@lem3486768 A B x f x') (@lem3486766 A g x')). Qed.
Lemma lem3486770 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term44 A B x f g) = (term100 A B x f g).
Proof. exact (fun_ext (fun x' : A => @lem3486769 A B x f g x')). Qed.
Lemma lem3486771 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3486872 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) : (term45 A B x f g) = (term101 A B x f g).
Proof. exact (MK_COMB (@lem3486771 A) (@lem3486770 A B x f g)). Qed.
Lemma lem3486873 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (h1 : term45 A B x f g) : term101 A B x f g.
Proof. exact (EQ_MP (@lem3486872 A B x f g) (@lem3486749 A B x f g h1)). Qed.
Lemma lem3486879 {A : Type'} (g : type686 A) (x' : A -> Prop) (h1 : g x') : g x'.
Proof. exact (h1). Qed.
Lemma lem3486886 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term102 A B x f x' x'') = (term103 A B x f x' x'').
Proof. exact (@lem17045 (x = (f x'')) (x' x'')). Qed.
Lemma lem3486887 {A : Type'} (P : A -> Prop) : (term104 A P) = (term105 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3486888 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term95 A B x f x') = (term106 A B x f x').
Proof. exact (@lem3486887 A (term70 A B x f x')). Qed.
Lemma lem3486889 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term107 A B x f x' x'') = (term68 A B x f x' x'').
Proof. exact (eq_refl (term107 A B x f x' x'')). Qed.
Lemma lem3486890 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3486891 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term108 A B x f x' x'') = (term102 A B x f x' x'').
Proof. exact (MK_COMB (@lem3486890) (@lem3486889 A B x f x' x'')). Qed.
Lemma lem3486892 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term108 A B x f x' x'') = (term103 A B x f x' x'').
Proof. exact (TRANS (@lem3486891 A B x f x' x'') (@lem3486886 A B x f x' x'')). Qed.
Lemma lem3486893 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term109 A B x f x') = (term110 A B x f x').
Proof. exact (fun_ext (fun x'' : A => @lem3486892 A B x f x' x'')). Qed.
Lemma lem3486894 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3486895 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term106 A B x f x') = (term111 A B x f x').
Proof. exact (MK_COMB (@lem3486894 A) (@lem3486893 A B x f x')). Qed.
Lemma lem3486948 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term95 A B x f x') = (term111 A B x f x').
Proof. exact (TRANS (@lem3486888 A B x f x') (@lem3486895 A B x f x')). Qed.
Lemma lem3486949 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (h1 : term95 A B x f x') : term111 A B x f x'.
Proof. exact (EQ_MP (@lem3486948 A B x f x') (@lem3486755 A B x f x' h1)). Qed.
Lemma lem3486950 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term99 A B x f g x''.
Proof. exact (h1). Qed.
Lemma lem3486955 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3486956 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3486955 (A -> Prop) Prop f x). Qed.
Lemma lem3486958 {A : Type'} (g : type686 A) (x' : A -> Prop) : (g x') = (@I ((A -> Prop) -> Prop) g x').
Proof. exact (@lem3486956 A g x'). Qed.
Lemma lem3486960 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3486965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3486966 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3486965 A Prop f x). Qed.
Lemma lem3486968 {A : Type'} (x' : A -> Prop) (x : A) : (x' x) = (@I (A -> Prop) x' x).
Proof. exact (@lem3486966 A x' x). Qed.
Lemma lem3486969 {A : Type'} (x' : A -> Prop) (x : A) : (term112 A x' x) = (term113 A x' x).
Proof. exact (MK_COMB (@lem3486960) (@lem3486968 A x' x)). Qed.
Lemma lem3486970 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3486977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3486979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3486977 A B f x). Qed.
Lemma lem3486980 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem3486981 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (x = (f x')) = (x = (@I (A -> B) f x')).
Proof. exact (MK_COMB (@lem3486980 B x) (@lem3486979 A B f x')). Qed.
Lemma lem3486982 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term114 A B x f x') = (term115 A B x f x').
Proof. exact (MK_COMB (@lem3486970) (@lem3486981 A B x f x')). Qed.
Lemma lem3486983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3486984 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term116 A B x f x') = (term117 A B x f x').
Proof. exact (MK_COMB (@lem3486983) (@lem3486982 A B x f x')). Qed.
Lemma lem3486985 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term103 A B x f x' x'') = (term118 A B x f x' x'').
Proof. exact (MK_COMB (@lem3486984 A B x f x'') (@lem3486969 A x' x'')). Qed.
Lemma lem3486986 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term110 A B x f x') = (term119 A B x f x').
Proof. exact (fun_ext (fun x'' : A => @lem3486985 A B x f x' x'')). Qed.
Lemma lem3486987 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3486988 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term111 A B x f x') = (term120 A B x f x').
Proof. exact (MK_COMB (@lem3486987 A) (@lem3486986 A B x f x')). Qed.
Lemma lem3486989 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (h1 : term95 A B x f x') : term120 A B x f x'.
Proof. exact (EQ_MP (@lem3486988 A B x f x') (@lem3486949 A B x f x' h1)). Qed.
Lemma lem3486994 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3486995 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3486994 A Prop f x). Qed.
Lemma lem3486997 {A : Type'} (t : A -> Prop) (x'' : A) : (t x'') = (@I (A -> Prop) t x'').
Proof. exact (@lem3486995 A t x''). Qed.
Lemma lem3486998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3487003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3487004 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3487003 (A -> Prop) Prop f x). Qed.
Lemma lem3487006 {A : Type'} (g : type686 A) (t : A -> Prop) : (g t) = (@I ((A -> Prop) -> Prop) g t).
Proof. exact (@lem3487004 A g t). Qed.
Lemma lem3487007 {A : Type'} (g : type686 A) (t : A -> Prop) : (term121 A g t) = (term122 A g t).
Proof. exact (MK_COMB (@lem3486998) (@lem3487006 A g t)). Qed.
Lemma lem3487008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3487009 {A : Type'} (g : type686 A) (t : A -> Prop) : (term123 A g t) = (term124 A g t).
Proof. exact (MK_COMB (@lem3487008) (@lem3487007 A g t)). Qed.
Lemma lem3487010 {A : Type'} (g : type686 A) (t : A -> Prop) (x'' : A) : (term96 A g t x'') = (term125 A g t x'').
Proof. exact (MK_COMB (@lem3487009 A g t) (@lem3486997 A t x'')). Qed.
Lemma lem3487011 {A : Type'} (g : type686 A) (x'' : A) : (term97 A g x'') = (term126 A g x'').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3487010 A g t x'')). Qed.
Lemma lem3487012 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3487013 {A : Type'} (g : type686 A) (x'' : A) : (term98 A g x'') = (term127 A g x'').
Proof. exact (MK_COMB (@lem3487012 A) (@lem3487011 A g x'')). Qed.
Lemma lem3487020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3487021 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3487020 A B f x). Qed.
Lemma lem3487023 {A B : Type'} (f : A -> B) (x'' : A) : (f x'') = (@I (A -> B) f x'').
Proof. exact (@lem3487021 A B f x''). Qed.
Lemma lem3487024 {B : Type'} (x : B) : (@eq B x) = (@eq B x).
Proof. exact (eq_refl (@eq B x)). Qed.
Lemma lem3487025 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (x = (f x'')) = (x = (@I (A -> B) f x'')).
Proof. exact (MK_COMB (@lem3487024 B x) (@lem3487023 A B f x'')). Qed.
Lemma lem3487026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3487027 {A B : Type'} (x : B) (f : A -> B) (x'' : A) : (term40 A B x f x'') = (term128 A B x f x'').
Proof. exact (MK_COMB (@lem3487026) (@lem3487025 A B x f x'')). Qed.
Lemma lem3487028 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x'' : A) : (term99 A B x f g x'') = (term129 A B x f g x'').
Proof. exact (MK_COMB (@lem3487027 A B x f x'') (@lem3487013 A g x'')). Qed.
Lemma lem3487029 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term129 A B x f g x''.
Proof. exact (EQ_MP (@lem3487028 A B x f g x'') (@lem3486950 A B x f g x'' h1)). Qed.
Lemma lem3487030 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term127 A g x''.
Proof. exact (proj2 (@lem3487029 A B x f g x'' h1)). Qed.
Lemma lem3487043 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (x'' : A) : (term118 A B x f x' x'') = (term118 A B x f x' x'').
Proof. exact (eq_refl (term118 A B x f x' x'')). Qed.
Lemma lem3487044 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term119 A B x f x') = (term119 A B x f x').
Proof. exact (fun_ext (fun x'' : A => @lem3487043 A B x f x' x'')). Qed.
Lemma lem3487045 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3487047 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) : (term120 A B x f x') = (term120 A B x f x').
Proof. exact (MK_COMB (@lem3487045 A) (@lem3487044 A B x f x')). Qed.
Lemma lem3487048 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (h1 : term95 A B x f x') : term120 A B x f x'.
Proof. exact (EQ_MP (@lem3487047 A B x f x') (@lem3486989 A B x f x' h1)). Qed.
Lemma lem3487060 {A : Type'} (g : type686 A) (t : A -> Prop) (x'' : A) : (term125 A g t x'') = (term125 A g t x'').
Proof. exact (eq_refl (term125 A g t x'')). Qed.
Lemma lem3487061 {A : Type'} (g : type686 A) (x'' : A) : (term126 A g x'') = (term126 A g x'').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3487060 A g t x'')). Qed.
Lemma lem3487062 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3487064 {A : Type'} (g : type686 A) (x'' : A) : (term127 A g x'') = (term127 A g x'').
Proof. exact (MK_COMB (@lem3487062 A) (@lem3487061 A g x'')). Qed.
Lemma lem3487065 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term127 A g x''.
Proof. exact (EQ_MP (@lem3487064 A g x'') (@lem3487030 A B x f g x'' h1)). Qed.
Lemma lem3487066 {A B : Type'} (_36721 : A) (x : B) (f : A -> B) (x' : A -> Prop) (h1 : term95 A B x f x') : term130 A B x f x' _36721.
Proof. exact (@lem3487048 A B x f x' h1 _36721). Qed.
Lemma lem3487067 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term130 A B x f x' _36721) = (term118 A B x f x' _36721).
Proof. exact (eq_refl (term130 A B x f x' _36721)). Qed.
Lemma lem3487069 {A B : Type'} (_36722 : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term131 A g x'' _36722.
Proof. exact (@lem3487065 A B x f g x'' h1 _36722). Qed.
Lemma lem3487070 {A : Type'} (g : type686 A) (_36722 : A -> Prop) (x'' : A) : (term131 A g x'' _36722) = (term125 A g _36722 x'').
Proof. exact (eq_refl (term131 A g x'' _36722)). Qed.
Lemma lem3487079 {A B : Type'} (_36721 : A) (x : B) (f : A -> B) (x' : A -> Prop) (h1 : term95 A B x f x') : term118 A B x f x' _36721.
Proof. exact (EQ_MP (@lem3487067 A B x f x' _36721) (@lem3487066 A B _36721 x f x' h1)). Qed.
Lemma lem3487081 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : x = (@I (A -> B) f x'').
Proof. exact (proj1 (@lem3487029 A B x f g x'' h1)). Qed.
Lemma lem3487116 {A B : Type'} (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term132 A B f x' _36721) = (term132 A B f x' _36721).
Proof. exact (eq_refl (term132 A B f x' _36721)). Qed.
Lemma lem3487117 {A B : Type'} (x' : A -> Prop) (_36721 : A) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : (term133 A B f x' _36721 x) = (term134 A B x' _36721 f x'').
Proof. exact (MK_COMB (@lem3487116 A B f x' _36721) (@lem3487081 A B x f g x'' h1)). Qed.
Lemma lem3487118 {A B : Type'} (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term134 A B x' _36721 f x'') = (term135 A B x'' f x' _36721).
Proof. exact (eq_refl (term134 A B x' _36721 f x'')). Qed.
Lemma lem3487119 {A B : Type'} (f : A -> B) (x' : A -> Prop) (_36721 : A) (x : B) : (term136 A B f x' _36721 x) = (term136 A B f x' _36721 x).
Proof. exact (eq_refl (term136 A B f x' _36721 x)). Qed.
Lemma lem3487120 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : ((term133 A B f x' _36721 x) = (term134 A B x' _36721 f x'')) = ((term133 A B f x' _36721 x) = (term135 A B x'' f x' _36721)).
Proof. exact (MK_COMB (@lem3487119 A B f x' _36721 x) (@lem3487118 A B x'' f x' _36721)). Qed.
Lemma lem3487121 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term133 A B f x' _36721 x) = (term118 A B x f x' _36721).
Proof. exact (eq_refl (term133 A B f x' _36721 x)). Qed.
Lemma lem3487122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3487123 {A B : Type'} (x : B) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term136 A B f x' _36721 x) = (term137 A B x f x' _36721).
Proof. exact (MK_COMB (@lem3487122) (@lem3487121 A B x f x' _36721)). Qed.
Lemma lem3487124 {A B : Type'} (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term135 A B x'' f x' _36721) = (term135 A B x'' f x' _36721).
Proof. exact (eq_refl (term135 A B x'' f x' _36721)). Qed.
Lemma lem3487125 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : ((term133 A B f x' _36721 x) = (term135 A B x'' f x' _36721)) = ((term118 A B x f x' _36721) = (term135 A B x'' f x' _36721)).
Proof. exact (MK_COMB (@lem3487123 A B x f x' _36721) (@lem3487124 A B x'' f x' _36721)). Qed.
Lemma lem3487126 {A B : Type'} (x : B) (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : ((term133 A B f x' _36721 x) = (term134 A B x' _36721 f x'')) = ((term118 A B x f x' _36721) = (term135 A B x'' f x' _36721)).
Proof. exact (TRANS (@lem3487120 A B x x'' f x' _36721) (@lem3487125 A B x x'' f x' _36721)). Qed.
Lemma lem3487127 {A B : Type'} (x' : A -> Prop) (_36721 : A) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : (term118 A B x f x' _36721) = (term135 A B x'' f x' _36721).
Proof. exact (EQ_MP (@lem3487126 A B x x'' f x' _36721) (@lem3487117 A B x' _36721 x f g x'' h1)). Qed.
Lemma lem3487128 {A B : Type'} (_36721 : A) (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term95 A B x f x') (h2 : term99 A B x f g x'') : term135 A B x'' f x' _36721.
Proof. exact (EQ_MP (@lem3487127 A B x' _36721 x f g x'' h2) (@lem3487079 A B _36721 x f x' h1)). Qed.
Lemma lem3487142 {A B : Type'} (_36722 : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term125 A g _36722 x''.
Proof. exact (EQ_MP (@lem3487070 A g _36722 x'') (@lem3487069 A B _36722 x f g x'' h1)). Qed.
Lemma lem3487207 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3487208 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3487207 B x). Qed.
Lemma lem3487209 {A B : Type'} (f : A -> B) (x'' : A) : (@I (A -> B) f x'') = (@I (A -> B) f x'').
Proof. exact (@lem3487208 B (@I (A -> B) f x'')). Qed.
Lemma lem3487210 {A B : Type'} (f : A -> B) (x'' : A) : term138 A B f x''.
Proof. exact (fun h0 : term139 A B f x'' => @lem3487209 A B f x''). Qed.
Lemma lem3487212 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3487213 {A B : Type'} (f : A -> B) (x'' : A) : (term138 A B f x'') = ((@I (A -> B) f x'') = (@I (A -> B) f x'')).
Proof. exact (@lem3487212 ((@I (A -> B) f x'') = (@I (A -> B) f x''))). Qed.
Lemma lem3487214 {A B : Type'} (f : A -> B) (x'' : A) : (@I (A -> B) f x'') = (@I (A -> B) f x'').
Proof. exact (EQ_MP (@lem3487213 A B f x'') (@lem3487210 A B f x'')). Qed.
Lemma lem3487216 {A : Type'} (g : type686 A) (x' : A -> Prop) (h1 : g x') : @I ((A -> Prop) -> Prop) g x'.
Proof. exact (EQ_MP (@lem3486958 A g x') (@lem3486879 A g x' h1)). Qed.
Lemma lem3487217 {A : Type'} (g : type686 A) (x' : A -> Prop) (h1 : g x') : term141 A g x'.
Proof. exact (fun h0 : term122 A g x' => @lem3487216 A g x' h1). Qed.
Lemma lem3487219 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3487220 {A : Type'} (g : type686 A) (x' : A -> Prop) : (term141 A g x') = (@I ((A -> Prop) -> Prop) g x').
Proof. exact (@lem3487219 (@I ((A -> Prop) -> Prop) g x')). Qed.
Lemma lem3487221 {A : Type'} (g : type686 A) (x' : A -> Prop) (h1 : g x') : @I ((A -> Prop) -> Prop) g x'.
Proof. exact (EQ_MP (@lem3487220 A g x') (@lem3487217 A g x' h1)). Qed.
Lemma lem3487227 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3487228 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : (term125 A g _36722 x'') = (term142 A x'' g _36722).
Proof. exact (@lem3487227 (@I (A -> Prop) _36722 x'') (term122 A g _36722)). Qed.
Lemma lem3487234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3487235 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : (term143 A g _36722 x'') = (term144 A x'' g _36722).
Proof. exact (MK_COMB (@lem3487234) (@lem3487228 A x'' g _36722)). Qed.
Lemma lem3487241 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : (term142 A x'' g _36722) = (term142 A x'' g _36722).
Proof. exact (eq_refl (term142 A x'' g _36722)). Qed.
Lemma lem3487242 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : ((term125 A g _36722 x'') = (term142 A x'' g _36722)) = ((term142 A x'' g _36722) = (term142 A x'' g _36722)).
Proof. exact (MK_COMB (@lem3487235 A x'' g _36722) (@lem3487241 A x'' g _36722)). Qed.
Lemma lem3487244 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3487245 (x : Prop) : (x = x) = True.
Proof. exact (@lem3487244 Prop x). Qed.
Lemma lem3487246 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : ((term142 A x'' g _36722) = (term142 A x'' g _36722)) = True.
Proof. exact (@lem3487245 (term142 A x'' g _36722)). Qed.
Lemma lem3487247 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : ((term125 A g _36722 x'') = (term142 A x'' g _36722)) = True.
Proof. exact (TRANS (@lem3487242 A x'' g _36722) (@lem3487246 A x'' g _36722)). Qed.
Lemma lem3487248 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : True = ((term125 A g _36722 x'') = (term142 A x'' g _36722)).
Proof. exact (SYM (@lem3487247 A x'' g _36722)). Qed.
Lemma lem3487249 {A : Type'} (x'' : A) (g : type686 A) (_36722 : A -> Prop) : (term125 A g _36722 x'') = (term142 A x'' g _36722).
Proof. exact (EQ_MP (@lem3487248 A x'' g _36722) (@lem0)). Qed.
Lemma lem3487250 {A B : Type'} (_36722 : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term142 A x'' g _36722.
Proof. exact (EQ_MP (@lem3487249 A x'' g _36722) (@lem3487142 A B _36722 x f g x'' h1)). Qed.
Lemma lem3487252 (b : Prop) (a : Prop) : (a \/ b) = (term145 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3487253 {A : Type'} (g : type686 A) (_36722 : A -> Prop) (x'' : A) : (term142 A x'' g _36722) = (term146 A g _36722 x'').
Proof. exact (@lem3487252 (term122 A g _36722) (@I (A -> Prop) _36722 x'')). Qed.
Lemma lem3487255 (a : Prop) : (term93 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3487256 {A : Type'} (g : type686 A) (_36722 : A -> Prop) : (term147 A g _36722) = (@I ((A -> Prop) -> Prop) g _36722).
Proof. exact (@lem3487255 (@I ((A -> Prop) -> Prop) g _36722)). Qed.
Lemma lem3487257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3487258 {A : Type'} (g : type686 A) (_36722 : A -> Prop) : (term148 A g _36722) = (term149 A g _36722).
Proof. exact (MK_COMB (@lem3487257) (@lem3487256 A g _36722)). Qed.
Lemma lem3487259 {A : Type'} (_36722 : A -> Prop) (x'' : A) : (@I (A -> Prop) _36722 x'') = (@I (A -> Prop) _36722 x'').
Proof. exact (eq_refl (@I (A -> Prop) _36722 x'')). Qed.
Lemma lem3487260 {A : Type'} (g : type686 A) (_36722 : A -> Prop) (x'' : A) : (term146 A g _36722 x'') = (term150 A g _36722 x'').
Proof. exact (MK_COMB (@lem3487258 A g _36722) (@lem3487259 A _36722 x'')). Qed.
Lemma lem3487261 {A : Type'} (g : type686 A) (_36722 : A -> Prop) (x'' : A) : (term142 A x'' g _36722) = (term150 A g _36722 x'').
Proof. exact (TRANS (@lem3487253 A g _36722 x'') (@lem3487260 A g _36722 x'')). Qed.
Lemma lem3487264 {A B : Type'} (_36722 : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term150 A g _36722 x''.
Proof. exact (EQ_MP (@lem3487261 A g _36722 x'') (@lem3487250 A B _36722 x f g x'' h1)). Qed.
Lemma lem3487265 {A B : Type'} (_36722 : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term150 A g _36722 x''.
Proof. exact (@lem3487264 A B _36722 x f g x'' h1). Qed.
Lemma lem3487266 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term99 A B x f g x'') : term150 A g x' x''.
Proof. exact (@lem3487265 A B x' x f g x'' h1). Qed.
Lemma lem3487269 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : g x') (h2 : term99 A B x f g x'') : @I (A -> Prop) x' x''.
Proof. exact (@lem3487266 A B x' x f g x'' h2 (@lem3487221 A g x' h1)). Qed.
Lemma lem3487270 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : g x') (h2 : term99 A B x f g x'') : term151 A x' x''.
Proof. exact (fun h0 : term113 A x' x'' => @lem3487269 A B x' x f g x'' h1 h2). Qed.
Lemma lem3487272 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3487273 {A : Type'} (x' : A -> Prop) (x'' : A) : (term151 A x' x'') = (@I (A -> Prop) x' x'').
Proof. exact (@lem3487272 (@I (A -> Prop) x' x'')). Qed.
Lemma lem3487274 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : g x') (h2 : term99 A B x f g x'') : @I (A -> Prop) x' x''.
Proof. exact (EQ_MP (@lem3487273 A x' x'') (@lem3487270 A B x' x f g x'' h1 h2)). Qed.
Lemma lem3487276 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3487277 {A B : Type'} (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term135 A B x'' f x' _36721) = (term154 A B x'' f x' _36721).
Proof. exact (@lem3487276 ((@I (A -> B) f x'') = (@I (A -> B) f _36721)) (@I (A -> Prop) x' _36721)). Qed.
Lemma lem3487279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3487280 {A B : Type'} (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term154 A B x'' f x' _36721) = (term155 A B x'' f x' _36721).
Proof. exact (@lem3487279 (term156 A B x'' f x' _36721)). Qed.
Lemma lem3487281 {A B : Type'} (x'' : A) (f : A -> B) (x' : A -> Prop) (_36721 : A) : (term135 A B x'' f x' _36721) = (term155 A B x'' f x' _36721).
Proof. exact (TRANS (@lem3487277 A B x'' f x' _36721) (@lem3487280 A B x'' f x' _36721)). Qed.
Lemma lem3487283 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : g x') (h2 : term99 A B x f g x'') : term157 A B f x' x''.
Proof. exact (conj (@lem3487214 A B f x'') (@lem3487274 A B x' x f g x'' h1 h2)). Qed.
Lemma lem3487285 {A B : Type'} (_36721 : A) (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term95 A B x f x') (h2 : term99 A B x f g x'') : term155 A B x'' f x' _36721.
Proof. exact (EQ_MP (@lem3487281 A B x'' f x' _36721) (@lem3487128 A B _36721 x' x f g x'' h1 h2)). Qed.
Lemma lem3487286 {A B : Type'} (_36721 : A) (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term95 A B x f x') (h2 : term99 A B x f g x'') : term155 A B x'' f x' _36721.
Proof. exact (@lem3487285 A B _36721 x' x f g x'' h1 h2). Qed.
Lemma lem3487287 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term95 A B x f x') (h2 : term99 A B x f g x'') : term158 A B f x' x''.
Proof. exact (@lem3487286 A B x'' x' x f g x'' h1 h2). Qed.
Lemma lem3487290 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term95 A B x f x') (h2 : g x') (h3 : term99 A B x f g x'') : False.
Proof. exact (@lem3487287 A B x' x f g x'' h1 h3 (@lem3487283 A B x' x f g x'' h2 h3)). Qed.
Lemma lem3487291 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term95 A B x f x') (h2 : g x') (h3 : term99 A B x f g x'') : term159.
Proof. exact (fun h0 : ~ False => @lem3487290 A B x' x f g x'' h1 h2 h3). Qed.
Lemma lem3487293 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3487294 : term159 = False.
Proof. exact (@lem3487293 False). Qed.
Lemma lem3487296 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (x'' : A) (h1 : term95 A B x f x') (h2 : g x') (h3 : term99 A B x f g x'') : False.
Proof. exact (EQ_MP (@lem3487294) (@lem3487291 A B x' x f g x'' h1 h2 h3)). Qed.
Lemma lem3487297 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A -> Prop) (h1 : term45 A B x f g) (h2 : term95 A B x f x') (h3 : g x') : False.
Proof. exact (ex_elim (@lem3486873 A B x f g h1) (fun x'' : A => fun h0 : term100 A B x f g x'' => @lem3487296 A B x' x f g x'' h2 h3 h0)). Qed.
Lemma lem3487298 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A -> Prop) (h1 : term45 A B x f g) (h2 : term95 A B x f x') (h3 : g x') : (g x') = False.
Proof. exact (prop_ext (fun h4 : g x' => @lem3487297 A B x f g x' h1 h2 h3) (fun h4 : False => @lem3486879 A g x' h3)). Qed.
Lemma lem3487299 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A -> Prop) (h1 : term45 A B x f g) (h2 : term95 A B x f x') (h3 : g x') : False.
Proof. exact (EQ_MP (@lem3487298 A B x f g x' h1 h2 h3) (@lem3486879 A g x' h3)). Qed.
Lemma lem3487300 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A -> Prop) (h1 : term45 A B x f g) (h2 : term95 A B x f x') (h3 : g x') : (term95 A B x f x') = False.
Proof. exact (prop_ext (fun h4 : term95 A B x f x' => @lem3487299 A B x f g x' h1 h2 h3) (fun h4 : False => @lem3486755 A B x f x' h2)). Qed.
Lemma lem3487301 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A -> Prop) (h1 : term45 A B x f g) (h2 : term95 A B x f x') (h3 : g x') : False.
Proof. exact (EQ_MP (@lem3487300 A B x f g x' h1 h2 h3) (@lem3486755 A B x f x' h2)). Qed.
Lemma lem3487302 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A -> Prop) (h1 : term45 A B x f g) (h2 : g x') : term94 A B x f x'.
Proof. exact (fun h0 : term95 A B x f x' => @lem3487301 A B x f g x' h1 h0 h2). Qed.
Lemma lem3487303 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (x' : A -> Prop) (h1 : term45 A B x f g) (h2 : g x') : term71 A B x f x'.
Proof. exact (EQ_MP (@lem3486754 A B x f x') (@lem3487302 A B x f g x' h1 h2)). Qed.
Lemma lem3487304 {A B : Type'} (x' : A -> Prop) (x : B) (f : A -> B) (g : type686 A) (h1 : term45 A B x f g) : term73 A B g x f x'.
Proof. exact (fun h0 : g x' => @lem3487303 A B x f g x' h1 h0). Qed.
Lemma lem3487309 {A B : Type'} (x : B) (f : A -> B) (g : type686 A) (h1 : term45 A B x f g) : term76 A B g x f.
Proof. exact (fun x' : A -> Prop => @lem3487304 A B x' x f g h1). Qed.
Lemma lem3487310 {A B : Type'} (g : type686 A) (x : B) (f : A -> B) : term78 A B g x f.
Proof. exact (fun h0 : term45 A B x f g => @lem3487309 A B x f g h0). Qed.
Lemma lem3487315 {A B : Type'} (g : type686 A) (f : A -> B) : term81 A B g f.
Proof. exact (fun x : B => @lem3487310 A B g x f). Qed.
Lemma lem3487320 {A B : Type'} (f : A -> B) : term83 A B f.
Proof. exact (fun g : type686 A => @lem3487315 A B g f). Qed.
Lemma lem3487325 {A B : Type'} : term85 A B.
Proof. exact (fun f : A -> B => @lem3487320 A B f). Qed.
Lemma lem3487326 {A B : Type'} : term87 A B.
Proof. exact (EQ_MP (@lem3486748 A B) (@lem3487325 A B)). Qed.
Lemma lem3487328 {A B : Type'} : term87 A B.
Proof. exact (@lem3486529 A B (@lem3487326 A B)). Qed.
Lemma lem3487329 {A B : Type'} (h1 : term88 A B) : False.
Proof. exact (@lem3487328 A B (@lem3486513 A B h1)). Qed.
Lemma lem3487330 {A B : Type'} (h1 : term88 A B) : (term88 A B) = False.
Proof. exact (prop_ext (fun h2 : term88 A B => @lem3487329 A B h1) (fun h2 : False => @lem3486513 A B h1)). Qed.
Lemma lem3487331 {A B : Type'} (h1 : term88 A B) : False.
Proof. exact (EQ_MP (@lem3487330 A B h1) (@lem3486513 A B h1)). Qed.
Lemma lem3487332 {A B : Type'} : term87 A B.
Proof. exact (fun h0 : term88 A B => @lem3487331 A B h0). Qed.
Lemma lem3487333 {A B : Type'} : term85 A B.
Proof. exact (EQ_MP (@lem3486512 A B) (@lem3487332 A B)). Qed.
Lemma lem3487334 {A B : Type'} : term26 A B.
Proof. exact (EQ_MP (@lem3486508 A B) (@lem3487333 A B)). Qed.
Lemma lem3487335 {A B : Type'} : term19 A B.
Proof. exact (EQ_MP (@lem3486339 A B) (@lem3487334 A B)). Qed.
Lemma lem3487336 {A B : Type'} : term18 A B.
Proof. exact (EQ_MP (@lem3486296 A B) (@lem3487335 A B)). Qed.
