Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import o_THM_term_abbrevs.
Require Import o_DEF_spec.
Lemma lem15399 {A B C : Type'} (f : B -> C) : term0 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem15400 {A B C : Type'} (f : B -> C) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem15401 {A B C : Type'} (f : B -> C) : term1 A B C f.
Proof. exact (EQ_MP (@lem15400 A B C f) (@lem15399 A B C f)). Qed.
Lemma lem15402 {A B C : Type'} (f : B -> C) (g : A -> B) : term2 A B C f g.
Proof. exact (@lem15401 A B C f g). Qed.
Lemma lem15403 {A B C : Type'} (f : B -> C) (g : A -> B) : (term2 A B C f g) = ((@o A B C f g) = (term3 A B C f g)).
Proof. exact (eq_refl (term2 A B C f g)). Qed.
Lemma lem15406 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (EQ_MP (@lem15403 A B C f g) (@lem15402 A B C f g)). Qed.
Lemma lem15407 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (@lem15406 A B C f g). Qed.
Lemma lem15408 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem15409 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (@o A B C f g x) = (term4 A B C f g x).
Proof. exact (MK_COMB (@lem15407 A B C f g) (@lem15408 A x)). Qed.
Lemma lem15410 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem15411 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term5 A B C f g x) = (term6 A B C f g x).
Proof. exact (MK_COMB (@lem15410 C) (@lem15409 A B C f g x)). Qed.
Lemma lem15412 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term7 A B C f g x) = (term7 A B C f g x).
Proof. exact (eq_refl (term7 A B C f g x)). Qed.
Lemma lem15413 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : ((@o A B C f g x) = (term7 A B C f g x)) = ((term4 A B C f g x) = (term7 A B C f g x)).
Proof. exact (MK_COMB (@lem15411 A B C f g x) (@lem15412 A B C f g x)). Qed.
Lemma lem15414 {A B C : Type'} (f : B -> C) (g : A -> B) : (term8 A B C f g) = (term9 A B C f g).
Proof. exact (fun_ext (fun x : A => @lem15413 A B C f g x)). Qed.
Lemma lem15415 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem15416 {A B C : Type'} (f : B -> C) (g : A -> B) : (term10 A B C f g) = (term11 A B C f g).
Proof. exact (MK_COMB (@lem15415 A) (@lem15414 A B C f g)). Qed.
Lemma lem15417 {A B C : Type'} (f : B -> C) : (term12 A B C f) = (term13 A B C f).
Proof. exact (fun_ext (fun g : A -> B => @lem15416 A B C f g)). Qed.
Lemma lem15418 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem15419 {A B C : Type'} (f : B -> C) : (term14 A B C f) = (term15 A B C f).
Proof. exact (MK_COMB (@lem15418 A B) (@lem15417 A B C f)). Qed.
Lemma lem15420 {A B C : Type'} : (term16 A B C) = (term17 A B C).
Proof. exact (fun_ext (fun f : B -> C => @lem15419 A B C f)). Qed.
Lemma lem15421 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem15422 {A B C : Type'} : (term18 A B C) = (term19 A B C).
Proof. exact (MK_COMB (@lem15421 B C) (@lem15420 A B C)). Qed.
Lemma lem15423 {A B C : Type'} : (term19 A B C) = (term18 A B C).
Proof. exact (SYM (@lem15422 A B C)). Qed.
Lemma lem15424 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term4 A B C f g x) = (term7 A B C f g x).
Proof. exact (eq_refl (term4 A B C f g x)). Qed.
Lemma lem15425 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem15426 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term6 A B C f g x) = (term20 A B C f g x).
Proof. exact (MK_COMB (@lem15425 C) (@lem15424 A B C f g x)). Qed.
Lemma lem15427 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term7 A B C f g x) = (term7 A B C f g x).
Proof. exact (eq_refl (term7 A B C f g x)). Qed.
Lemma lem15428 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : ((term4 A B C f g x) = (term7 A B C f g x)) = ((term7 A B C f g x) = (term7 A B C f g x)).
Proof. exact (MK_COMB (@lem15426 A B C f g x) (@lem15427 A B C f g x)). Qed.
Lemma lem15429 {A B C : Type'} (f : B -> C) (g : A -> B) : (term9 A B C f g) = (term21 A B C f g).
Proof. exact (fun_ext (fun x : A => @lem15428 A B C f g x)). Qed.
Lemma lem15430 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem15431 {A B C : Type'} (f : B -> C) (g : A -> B) : (term11 A B C f g) = (term22 A B C f g).
Proof. exact (MK_COMB (@lem15430 A) (@lem15429 A B C f g)). Qed.
Lemma lem15432 {A B C : Type'} (f : B -> C) : (term13 A B C f) = (term23 A B C f).
Proof. exact (fun_ext (fun g : A -> B => @lem15431 A B C f g)). Qed.
Lemma lem15433 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem15434 {A B C : Type'} (f : B -> C) : (term15 A B C f) = (term24 A B C f).
Proof. exact (MK_COMB (@lem15433 A B) (@lem15432 A B C f)). Qed.
Lemma lem15435 {A B C : Type'} : (term17 A B C) = (term25 A B C).
Proof. exact (fun_ext (fun f : B -> C => @lem15434 A B C f)). Qed.
Lemma lem15436 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem15437 {A B C : Type'} : (term19 A B C) = (term26 A B C).
Proof. exact (MK_COMB (@lem15436 B C) (@lem15435 A B C)). Qed.
Lemma lem15438 {A B C : Type'} : (term26 A B C) = (term19 A B C).
Proof. exact (SYM (@lem15437 A B C)). Qed.
Lemma lem15439 {A B C : Type'} (f : B -> C) (g : A -> B) (x : A) : (term7 A B C f g x) = (term7 A B C f g x).
Proof. exact (eq_refl (term7 A B C f g x)). Qed.
Lemma lem15444 {A B C : Type'} (f : B -> C) (g : A -> B) : term22 A B C f g.
Proof. exact (fun x : A => @lem15439 A B C f g x). Qed.
Lemma lem15449 {A B C : Type'} (f : B -> C) : term24 A B C f.
Proof. exact (fun g : A -> B => @lem15444 A B C f g). Qed.
Lemma lem15454 {A B C : Type'} : term26 A B C.
Proof. exact (fun f : B -> C => @lem15449 A B C f). Qed.
Lemma lem15455 {A B C : Type'} : term19 A B C.
Proof. exact (EQ_MP (@lem15438 A B C) (@lem15454 A B C)). Qed.
Lemma lem15456 {A B C : Type'} : term18 A B C.
Proof. exact (EQ_MP (@lem15423 A B C) (@lem15455 A B C)). Qed.
