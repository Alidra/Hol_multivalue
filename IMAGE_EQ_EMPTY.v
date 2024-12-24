Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_EQ_EMPTY_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm82_spec.
Lemma lem3384558 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3384559 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem3384560 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem3384559 A B y) (@lem3384558 A B y)). Qed.
Lemma lem3384561 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem3384560 A B y s). Qed.
Lemma lem3384562 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem3384563 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem3384562 A B y s) (@lem3384561 A B y s)). Qed.
Lemma lem3384564 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem3384563 A B y s f). Qed.
Lemma lem3384565 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem3384567 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3384568 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem3384569 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem3384568 A x) (@lem3384567 A x)). Qed.
Lemma lem3384570 {A : Type'} (x : A) : term9 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3384572 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3384573 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem3384574 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem3384573 A s) (@lem3384572 A s)). Qed.
Lemma lem3384575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (@lem3384574 A s t). Qed.
Lemma lem3384576 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = ((s = t) = (term13 A s t)).
Proof. exact (eq_refl (term12 A s t)). Qed.
Lemma lem3384593 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term13 A s t).
Proof. exact (EQ_MP (@lem3384576 A s t) (@lem3384575 A s t)). Qed.
Lemma lem3384594 {_87928 : Type'} (s : _87928 -> Prop) (t : _87928 -> Prop) : (s = t) = (term13 _87928 s t).
Proof. exact (@lem3384593 _87928 s t). Qed.
Lemma lem3384595 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : ((@IMAGE _87932 _87928 f s) = (@EMPTY _87928)) = (term14 _87928 _87932 f s).
Proof. exact (@lem3384594 _87928 (@IMAGE _87932 _87928 f s) (@EMPTY _87928)). Qed.
Lemma lem3384605 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem3384565 A B y f s) (@lem3384564 A B y s f)). Qed.
Lemma lem3384606 {_87928 _87932 : Type'} (y : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term15 _87928 _87932 y f s) = (term16 _87928 _87932 y f s).
Proof. exact (@lem3384605 _87932 _87928 y f s). Qed.
Lemma lem3384607 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term15 _87928 _87932 x f s) = (term16 _87928 _87932 x f s).
Proof. exact (@lem3384606 _87928 _87932 x f s). Qed.
Lemma lem3384618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3384619 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term17 _87928 _87932 x f s) = (term18 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3384618) (@lem3384607 _87928 _87932 x f s)). Qed.
Lemma lem3384621 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3384570 A x (@lem3384569 A x)). Qed.
Lemma lem3384622 {_87928 : Type'} (x : _87928) : (@IN _87928 x (@EMPTY _87928)) = False.
Proof. exact (@lem3384621 _87928 x). Qed.
Lemma lem3384623 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term15 _87928 _87932 x f s) = (@IN _87928 x (@EMPTY _87928))) = ((term16 _87928 _87932 x f s) = False).
Proof. exact (MK_COMB (@lem3384619 _87928 _87932 x f s) (@lem3384622 _87928 x)). Qed.
Lemma lem3384625 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3384626 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term16 _87928 _87932 x f s) = False) = (term19 _87928 _87932 x f s).
Proof. exact (@lem3384625 (term16 _87928 _87932 x f s)). Qed.
Lemma lem3384637 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term15 _87928 _87932 x f s) = (@IN _87928 x (@EMPTY _87928))) = (term19 _87928 _87932 x f s).
Proof. exact (TRANS (@lem3384623 _87928 _87932 x f s) (@lem3384626 _87928 _87932 x f s)). Qed.
Lemma lem3384638 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term20 _87928 _87932 f s) = (term21 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3384637 _87928 _87932 x f s)). Qed.
Lemma lem3384639 {_87928 : Type'} : (@all _87928) = (@all _87928).
Proof. exact (eq_refl (@all _87928)). Qed.
Lemma lem3384640 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term14 _87928 _87932 f s) = (term22 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384639 _87928) (@lem3384638 _87928 _87932 f s)). Qed.
Lemma lem3384645 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : ((@IMAGE _87932 _87928 f s) = (@EMPTY _87928)) = (term22 _87928 _87932 f s).
Proof. exact (TRANS (@lem3384595 _87928 _87932 f s) (@lem3384640 _87928 _87932 f s)). Qed.
Lemma lem3384646 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3384647 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term23 _87928 _87932 f s) = (term24 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384646) (@lem3384645 _87928 _87932 f s)). Qed.
Lemma lem3384651 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term13 A s t).
Proof. exact (EQ_MP (@lem3384576 A s t) (@lem3384575 A s t)). Qed.
Lemma lem3384652 {_87932 : Type'} (s : _87932 -> Prop) (t : _87932 -> Prop) : (s = t) = (term13 _87932 s t).
Proof. exact (@lem3384651 _87932 s t). Qed.
Lemma lem3384653 {_87932 : Type'} (s : _87932 -> Prop) : (s = (@EMPTY _87932)) = (term25 _87932 s).
Proof. exact (@lem3384652 _87932 s (@EMPTY _87932)). Qed.
Lemma lem3384663 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3384570 A x (@lem3384569 A x)). Qed.
Lemma lem3384664 {_87932 : Type'} (x : _87932) : (@IN _87932 x (@EMPTY _87932)) = False.
Proof. exact (@lem3384663 _87932 x). Qed.
Lemma lem3384665 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term26 _87932 x s) = (term26 _87932 x s).
Proof. exact (eq_refl (term26 _87932 x s)). Qed.
Lemma lem3384666 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : ((@IN _87932 x s) = (@IN _87932 x (@EMPTY _87932))) = ((@IN _87932 x s) = False).
Proof. exact (MK_COMB (@lem3384665 _87932 x s) (@lem3384664 _87932 x)). Qed.
Lemma lem3384668 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3384669 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : ((@IN _87932 x s) = False) = (term27 _87932 x s).
Proof. exact (@lem3384668 (@IN _87932 x s)). Qed.
Lemma lem3384670 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : ((@IN _87932 x s) = (@IN _87932 x (@EMPTY _87932))) = (term27 _87932 x s).
Proof. exact (TRANS (@lem3384666 _87932 x s) (@lem3384669 _87932 x s)). Qed.
Lemma lem3384671 {_87932 : Type'} (s : _87932 -> Prop) : (term28 _87932 s) = (term29 _87932 s).
Proof. exact (fun_ext (fun x : _87932 => @lem3384670 _87932 x s)). Qed.
Lemma lem3384672 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3384673 {_87932 : Type'} (s : _87932 -> Prop) : (term25 _87932 s) = (term30 _87932 s).
Proof. exact (MK_COMB (@lem3384672 _87932) (@lem3384671 _87932 s)). Qed.
Lemma lem3384678 {_87932 : Type'} (s : _87932 -> Prop) : (s = (@EMPTY _87932)) = (term30 _87932 s).
Proof. exact (TRANS (@lem3384653 _87932 s) (@lem3384673 _87932 s)). Qed.
Lemma lem3384679 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (((@IMAGE _87932 _87928 f s) = (@EMPTY _87928)) = (s = (@EMPTY _87932))) = ((term22 _87928 _87932 f s) = (term30 _87932 s)).
Proof. exact (MK_COMB (@lem3384647 _87928 _87932 f s) (@lem3384678 _87932 s)). Qed.
Lemma lem3384684 {_87928 _87932 : Type'} (f : _87932 -> _87928) : (term31 _87928 _87932 f) = (term32 _87928 _87932 f).
Proof. exact (fun_ext (fun s : _87932 -> Prop => @lem3384679 _87928 _87932 f s)). Qed.
Lemma lem3384685 {_87932 : Type'} : (@all (_87932 -> Prop)) = (@all (_87932 -> Prop)).
Proof. exact (eq_refl (@all (_87932 -> Prop))). Qed.
Lemma lem3384686 {_87928 _87932 : Type'} (f : _87932 -> _87928) : (term33 _87928 _87932 f) = (term34 _87928 _87932 f).
Proof. exact (MK_COMB (@lem3384685 _87932) (@lem3384684 _87928 _87932 f)). Qed.
Lemma lem3384691 {_87928 _87932 : Type'} : (term35 _87928 _87932) = (term36 _87928 _87932).
Proof. exact (fun_ext (fun f : _87932 -> _87928 => @lem3384686 _87928 _87932 f)). Qed.
Lemma lem3384692 {_87928 _87932 : Type'} : (@all (_87932 -> _87928)) = (@all (_87932 -> _87928)).
Proof. exact (eq_refl (@all (_87932 -> _87928))). Qed.
Lemma lem3384693 {_87928 _87932 : Type'} : (term37 _87928 _87932) = (term38 _87928 _87932).
Proof. exact (MK_COMB (@lem3384692 _87928 _87932) (@lem3384691 _87928 _87932)). Qed.
Lemma lem3384698 {_87928 _87932 : Type'} : (term38 _87928 _87932) = (term37 _87928 _87932).
Proof. exact (SYM (@lem3384693 _87928 _87932)). Qed.
Lemma lem3384700 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3384701 {_87928 _87932 : Type'} : (term38 _87928 _87932) = (term40 _87928 _87932).
Proof. exact (@lem3384700 (term38 _87928 _87932)). Qed.
Lemma lem3384702 {_87928 _87932 : Type'} : (term40 _87928 _87932) = (term38 _87928 _87932).
Proof. exact (SYM (@lem3384701 _87928 _87932)). Qed.
Lemma lem3384703 {_87928 _87932 : Type'} (h1 : term41 _87928 _87932) : term41 _87928 _87932.
Proof. exact (h1). Qed.
Lemma lem3384706 {_87928 _87932 : Type'} (h1 : term40 _87928 _87932) : term40 _87928 _87932.
Proof. exact (h1). Qed.
Lemma lem3384707 {_87928 _87932 : Type'} : term42 _87928 _87932.
Proof. exact (fun h0 : term40 _87928 _87932 => @lem3384706 _87928 _87932 h0). Qed.
Lemma lem3384708 {_87928 _87932 : Type'} (h1 : term42 _87928 _87932) : term42 _87928 _87932.
Proof. exact (h1). Qed.
Lemma lem3384709 {_87928 _87932 : Type'} (h1 : term40 _87928 _87932) : term40 _87928 _87932.
Proof. exact (h1). Qed.
Lemma lem3384710 {_87928 _87932 : Type'} (h1 : term40 _87928 _87932) (h2 : term42 _87928 _87932) : term40 _87928 _87932.
Proof. exact (@lem3384708 _87928 _87932 h2 (@lem3384709 _87928 _87932 h1)). Qed.
Lemma lem3384711 {_87928 _87932 : Type'} (h1 : term40 _87928 _87932) : term43 _87928 _87932.
Proof. exact (fun h0 : term42 _87928 _87932 => @lem3384710 _87928 _87932 h1 h0). Qed.
Lemma lem3384712 {_87928 _87932 : Type'} (h1 : term42 _87928 _87932) : term42 _87928 _87932.
Proof. exact (h1). Qed.
Lemma lem3384713 {_87928 _87932 : Type'} (h1 : term40 _87928 _87932) (h2 : term42 _87928 _87932) : term40 _87928 _87932.
Proof. exact (@lem3384711 _87928 _87932 h1 (@lem3384712 _87928 _87932 h2)). Qed.
Lemma lem3384714 {_87928 _87932 : Type'} (h1 : term42 _87928 _87932) : term42 _87928 _87932.
Proof. exact (fun h0 : term40 _87928 _87932 => @lem3384713 _87928 _87932 h0 h1). Qed.
Lemma lem3384715 {_87928 _87932 : Type'} : term44 _87928 _87932.
Proof. exact (fun h0 : term42 _87928 _87932 => @lem3384714 _87928 _87932 h0). Qed.
Lemma lem3384718 {_87928 _87932 : Type'} : term42 _87928 _87932.
Proof. exact (@lem3384715 _87928 _87932 (@lem3384707 _87928 _87932)). Qed.
Lemma lem3384719 {_87928 _87932 : Type'} : term42 _87928 _87932.
Proof. exact (@lem3384718 _87928 _87932). Qed.
Lemma lem3384721 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3384722 {_87928 _87932 : Type'} : (term40 _87928 _87932) = (term45 _87928 _87932).
Proof. exact (@lem3384721 (term41 _87928 _87932)). Qed.
Lemma lem3384724 (t : Prop) : (term46 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3384725 {_87928 _87932 : Type'} : (term45 _87928 _87932) = (term38 _87928 _87932).
Proof. exact (@lem3384724 (term38 _87928 _87932)). Qed.
Lemma lem3384796 {_87928 _87932 : Type'} : (term40 _87928 _87932) = (term38 _87928 _87932).
Proof. exact (TRANS (@lem3384722 _87928 _87932) (@lem3384725 _87928 _87932)). Qed.
Lemma lem3384799 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term27 _87932 x s) = (term27 _87932 x s).
Proof. exact (eq_refl (term27 _87932 x s)). Qed.
Lemma lem3384800 {_87932 : Type'} (s : _87932 -> Prop) : (term29 _87932 s) = (term29 _87932 s).
Proof. exact (fun_ext (fun x : _87932 => @lem3384799 _87932 x s)). Qed.
Lemma lem3384801 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3384802 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (MK_COMB (@lem3384801 _87932) (@lem3384800 _87932 s)). Qed.
Lemma lem3384807 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term47 _87928 _87932 x f x' s) = (term47 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term47 _87928 _87932 x f x' s)). Qed.
Lemma lem3384808 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term48 _87928 _87932 x f s) = (term48 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3384807 _87928 _87932 x f x' s)). Qed.
Lemma lem3384809 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3384810 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term16 _87928 _87932 x f s) = (term16 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3384809 _87932) (@lem3384808 _87928 _87932 x f s)). Qed.
Lemma lem3384811 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3384812 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term19 _87928 _87932 x f s) = (term19 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3384811) (@lem3384810 _87928 _87932 x f s)). Qed.
Lemma lem3384813 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term21 _87928 _87932 f s) = (term21 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3384812 _87928 _87932 x f s)). Qed.
Lemma lem3384814 {_87928 : Type'} : (@all _87928) = (@all _87928).
Proof. exact (eq_refl (@all _87928)). Qed.
Lemma lem3384815 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term22 _87928 _87932 f s) = (term22 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384814 _87928) (@lem3384813 _87928 _87932 f s)). Qed.
Lemma lem3384816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3384817 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term24 _87928 _87932 f s) = (term24 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384816) (@lem3384815 _87928 _87932 f s)). Qed.
Lemma lem3384818 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term22 _87928 _87932 f s) = (term30 _87932 s)) = ((term22 _87928 _87932 f s) = (term30 _87932 s)).
Proof. exact (MK_COMB (@lem3384817 _87928 _87932 f s) (@lem3384802 _87932 s)). Qed.
Lemma lem3384819 {_87928 _87932 : Type'} (f : _87932 -> _87928) : (term32 _87928 _87932 f) = (term32 _87928 _87932 f).
Proof. exact (fun_ext (fun s : _87932 -> Prop => @lem3384818 _87928 _87932 f s)). Qed.
Lemma lem3384820 {_87932 : Type'} : (@all (_87932 -> Prop)) = (@all (_87932 -> Prop)).
Proof. exact (eq_refl (@all (_87932 -> Prop))). Qed.
Lemma lem3384821 {_87928 _87932 : Type'} (f : _87932 -> _87928) : (term34 _87928 _87932 f) = (term34 _87928 _87932 f).
Proof. exact (MK_COMB (@lem3384820 _87932) (@lem3384819 _87928 _87932 f)). Qed.
Lemma lem3384822 {_87928 _87932 : Type'} : (term36 _87928 _87932) = (term36 _87928 _87932).
Proof. exact (fun_ext (fun f : _87932 -> _87928 => @lem3384821 _87928 _87932 f)). Qed.
Lemma lem3384823 {_87928 _87932 : Type'} : (@all (_87932 -> _87928)) = (@all (_87932 -> _87928)).
Proof. exact (eq_refl (@all (_87932 -> _87928))). Qed.
Lemma lem3384824 {_87928 _87932 : Type'} : (term38 _87928 _87932) = (term38 _87928 _87932).
Proof. exact (MK_COMB (@lem3384823 _87928 _87932) (@lem3384822 _87928 _87932)). Qed.
Lemma lem3384859 {_87928 _87932 : Type'} : (term40 _87928 _87932) = (term38 _87928 _87932).
Proof. exact (TRANS (@lem3384796 _87928 _87932) (@lem3384824 _87928 _87932)). Qed.
Lemma lem3384860 {_87928 _87932 : Type'} : (term38 _87928 _87932) = (term40 _87928 _87932).
Proof. exact (SYM (@lem3384859 _87928 _87932)). Qed.
Lemma lem3384862 (p : Prop) : p = (term39 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3384863 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term22 _87928 _87932 f s) = (term30 _87932 s)) = (term49 _87928 _87932 f s).
Proof. exact (@lem3384862 ((term22 _87928 _87932 f s) = (term30 _87932 s))). Qed.
Lemma lem3384864 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term49 _87928 _87932 f s) = ((term22 _87928 _87932 f s) = (term30 _87932 s)).
Proof. exact (SYM (@lem3384863 _87928 _87932 f s)). Qed.
Lemma lem3384865 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term50 _87928 _87932 f s) : term50 _87928 _87932 f s.
Proof. exact (h1). Qed.
Lemma lem3384874 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term51 _87928 _87932 x f x' s) = (term52 _87928 _87932 x f x' s).
Proof. exact (@lem17045 (x = (f x')) (@IN _87932 x' s)). Qed.
Lemma lem3384877 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term47 _87928 _87932 x f x' s) = (term47 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term47 _87928 _87932 x f x' s)). Qed.
Lemma lem3384878 {_87932 : Type'} (P : _87932 -> Prop) : (term53 _87932 P) = (term54 _87932 P).
Proof. exact (@lem18394 _87932 P). Qed.
Lemma lem3384879 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term19 _87928 _87932 x f s) = (term55 _87928 _87932 x f s).
Proof. exact (@lem3384878 _87932 (term48 _87928 _87932 x f s)). Qed.
Lemma lem3384880 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term56 _87928 _87932 x f s x') = (term47 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term56 _87928 _87932 x f s x')). Qed.
Lemma lem3384881 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3384882 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term57 _87928 _87932 x f s x') = (term51 _87928 _87932 x f x' s).
Proof. exact (MK_COMB (@lem3384881) (@lem3384880 _87928 _87932 x f x' s)). Qed.
Lemma lem3384883 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term57 _87928 _87932 x f s x') = (term52 _87928 _87932 x f x' s).
Proof. exact (TRANS (@lem3384882 _87928 _87932 x f x' s) (@lem3384874 _87928 _87932 x f x' s)). Qed.
Lemma lem3384884 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term58 _87928 _87932 x f s) = (term59 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3384883 _87928 _87932 x f x' s)). Qed.
Lemma lem3384885 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3384886 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term55 _87928 _87932 x f s) = (term60 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3384885 _87932) (@lem3384884 _87928 _87932 x f s)). Qed.
Lemma lem3384887 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term19 _87928 _87932 x f s) = (term60 _87928 _87932 x f s).
Proof. exact (TRANS (@lem3384879 _87928 _87932 x f s) (@lem3384886 _87928 _87932 x f s)). Qed.
Lemma lem3384888 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term48 _87928 _87932 x f s) = (term48 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3384877 _87928 _87932 x f x' s)). Qed.
Lemma lem3384889 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3384890 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term16 _87928 _87932 x f s) = (term16 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3384889 _87932) (@lem3384888 _87928 _87932 x f s)). Qed.
Lemma lem3384891 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term61 _87928 _87932 x f s) = (term16 _87928 _87932 x f s).
Proof. exact (@lem16933 (term16 _87928 _87932 x f s)). Qed.
Lemma lem3384892 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term61 _87928 _87932 x f s) = (term16 _87928 _87932 x f s).
Proof. exact (TRANS (@lem3384891 _87928 _87932 x f s) (@lem3384890 _87928 _87932 x f s)). Qed.
Lemma lem3384893 {_87928 : Type'} (P : _87928 -> Prop) : (term62 _87928 P) = (term63 _87928 P).
Proof. exact (@lem18392 _87928 P). Qed.
Lemma lem3384894 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term64 _87928 _87932 f s) = (term65 _87928 _87932 f s).
Proof. exact (@lem3384893 _87928 (term21 _87928 _87932 f s)). Qed.
Lemma lem3384895 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term66 _87928 _87932 f s x) = (term19 _87928 _87932 x f s).
Proof. exact (eq_refl (term66 _87928 _87932 f s x)). Qed.
Lemma lem3384896 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3384897 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term67 _87928 _87932 f s x) = (term61 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3384896) (@lem3384895 _87928 _87932 x f s)). Qed.
Lemma lem3384898 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term67 _87928 _87932 f s x) = (term16 _87928 _87932 x f s).
Proof. exact (TRANS (@lem3384897 _87928 _87932 x f s) (@lem3384892 _87928 _87932 x f s)). Qed.
Lemma lem3384899 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term68 _87928 _87932 f s) = (term69 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3384898 _87928 _87932 x f s)). Qed.
Lemma lem3384900 {_87928 : Type'} : (@ex _87928) = (@ex _87928).
Proof. exact (eq_refl (@ex _87928)). Qed.
Lemma lem3384901 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term65 _87928 _87932 f s) = (term70 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384900 _87928) (@lem3384899 _87928 _87932 f s)). Qed.
Lemma lem3384902 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term64 _87928 _87932 f s) = (term70 _87928 _87932 f s).
Proof. exact (TRANS (@lem3384894 _87928 _87932 f s) (@lem3384901 _87928 _87932 f s)). Qed.
Lemma lem3384903 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term21 _87928 _87932 f s) = (term71 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3384887 _87928 _87932 x f s)). Qed.
Lemma lem3384904 {_87928 : Type'} : (@all _87928) = (@all _87928).
Proof. exact (eq_refl (@all _87928)). Qed.
Lemma lem3384905 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term22 _87928 _87932 f s) = (term72 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384904 _87928) (@lem3384903 _87928 _87932 f s)). Qed.
Lemma lem3384906 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term27 _87932 x s) = (term27 _87932 x s).
Proof. exact (eq_refl (term27 _87932 x s)). Qed.
Lemma lem3384909 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term73 _87932 x s) = (@IN _87932 x s).
Proof. exact (@lem16933 (@IN _87932 x s)). Qed.
Lemma lem3384910 {_87932 : Type'} (P : _87932 -> Prop) : (term62 _87932 P) = (term63 _87932 P).
Proof. exact (@lem18392 _87932 P). Qed.
Lemma lem3384911 {_87932 : Type'} (s : _87932 -> Prop) : (term74 _87932 s) = (term75 _87932 s).
Proof. exact (@lem3384910 _87932 (term29 _87932 s)). Qed.
Lemma lem3384912 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term76 _87932 s x) = (term27 _87932 x s).
Proof. exact (eq_refl (term76 _87932 s x)). Qed.
Lemma lem3384913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3384914 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term77 _87932 s x) = (term73 _87932 x s).
Proof. exact (MK_COMB (@lem3384913) (@lem3384912 _87932 x s)). Qed.
Lemma lem3384915 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term77 _87932 s x) = (@IN _87932 x s).
Proof. exact (TRANS (@lem3384914 _87932 x s) (@lem3384909 _87932 x s)). Qed.
Lemma lem3384916 {_87932 : Type'} (s : _87932 -> Prop) : (term78 _87932 s) = (term79 _87932 s).
Proof. exact (fun_ext (fun x : _87932 => @lem3384915 _87932 x s)). Qed.
Lemma lem3384917 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3384918 {_87932 : Type'} (s : _87932 -> Prop) : (term75 _87932 s) = (term80 _87932 s).
Proof. exact (MK_COMB (@lem3384917 _87932) (@lem3384916 _87932 s)). Qed.
Lemma lem3384919 {_87932 : Type'} (s : _87932 -> Prop) : (term74 _87932 s) = (term80 _87932 s).
Proof. exact (TRANS (@lem3384911 _87932 s) (@lem3384918 _87932 s)). Qed.
Lemma lem3384920 {_87932 : Type'} (s : _87932 -> Prop) : (term29 _87932 s) = (term29 _87932 s).
Proof. exact (fun_ext (fun x : _87932 => @lem3384906 _87932 x s)). Qed.
Lemma lem3384921 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3384922 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (MK_COMB (@lem3384921 _87932) (@lem3384920 _87932 s)). Qed.
Lemma lem3384923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3384924 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term81 _87928 _87932 f s) = (term82 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384923) (@lem3384902 _87928 _87932 f s)). Qed.
Lemma lem3384925 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term83 _87928 _87932 f s) = (term84 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384924 _87928 _87932 f s) (@lem3384922 _87932 s)). Qed.
Lemma lem3384926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3384927 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term85 _87928 _87932 f s) = (term86 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384926) (@lem3384905 _87928 _87932 f s)). Qed.
Lemma lem3384928 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term87 _87928 _87932 f s) = (term88 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384927 _87928 _87932 f s) (@lem3384919 _87932 s)). Qed.
Lemma lem3384929 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3384930 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term89 _87928 _87932 f s) = (term90 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384929) (@lem3384928 _87928 _87932 f s)). Qed.
Lemma lem3384931 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term91 _87928 _87932 f s) = (term92 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3384930 _87928 _87932 f s) (@lem3384925 _87928 _87932 f s)). Qed.
Lemma lem3384932 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term50 _87928 _87932 f s) = (term91 _87928 _87932 f s).
Proof. exact (@lem17646 (term22 _87928 _87932 f s) (term30 _87932 s)). Qed.
Lemma lem3384933 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term50 _87928 _87932 f s) = (term92 _87928 _87932 f s).
Proof. exact (TRANS (@lem3384932 _87928 _87932 f s) (@lem3384931 _87928 _87932 f s)). Qed.
Lemma lem3385048 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3385049 {_87932 : Type'} (P : Prop) (Q : _87932 -> Prop) : (term93 _87932 P Q) = (term94 _87932 P Q).
Proof. exact (@lem3385048 _87932 P Q). Qed.
Lemma lem3385050 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term95 _87928 _87932 f s) = (term96 _87928 _87932 f s).
Proof. exact (@lem3385049 _87932 (term72 _87928 _87932 f s) (term79 _87932 s)). Qed.
Lemma lem3385051 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term97 _87932 s x) = (@IN _87932 x s).
Proof. exact (eq_refl (term97 _87932 s x)). Qed.
Lemma lem3385052 {_87932 : Type'} (s : _87932 -> Prop) : (term98 _87932 s) = (term79 _87932 s).
Proof. exact (fun_ext (fun x : _87932 => @lem3385051 _87932 x s)). Qed.
Lemma lem3385053 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385054 {_87932 : Type'} (s : _87932 -> Prop) : (term99 _87932 s) = (term80 _87932 s).
Proof. exact (MK_COMB (@lem3385053 _87932) (@lem3385052 _87932 s)). Qed.
Lemma lem3385055 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term86 _87928 _87932 f s) = (term86 _87928 _87932 f s).
Proof. exact (eq_refl (term86 _87928 _87932 f s)). Qed.
Lemma lem3385056 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term95 _87928 _87932 f s) = (term88 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385055 _87928 _87932 f s) (@lem3385054 _87932 s)). Qed.
Lemma lem3385057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385058 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term100 _87928 _87932 f s) = (term101 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385057) (@lem3385056 _87928 _87932 f s)). Qed.
Lemma lem3385059 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term97 _87932 s x) = (@IN _87932 x s).
Proof. exact (eq_refl (term97 _87932 s x)). Qed.
Lemma lem3385060 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term86 _87928 _87932 f s) = (term86 _87928 _87932 f s).
Proof. exact (eq_refl (term86 _87928 _87932 f s)). Qed.
Lemma lem3385061 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term102 _87928 _87932 f s x) = (term103 _87928 _87932 f x s).
Proof. exact (MK_COMB (@lem3385060 _87928 _87932 f s) (@lem3385059 _87932 x s)). Qed.
Lemma lem3385062 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term104 _87928 _87932 f s) = (term105 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87932 => @lem3385061 _87928 _87932 f x s)). Qed.
Lemma lem3385063 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385064 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term96 _87928 _87932 f s) = (term106 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385063 _87932) (@lem3385062 _87928 _87932 f s)). Qed.
Lemma lem3385065 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term95 _87928 _87932 f s) = (term96 _87928 _87932 f s)) = ((term88 _87928 _87932 f s) = (term106 _87928 _87932 f s)).
Proof. exact (MK_COMB (@lem3385058 _87928 _87932 f s) (@lem3385064 _87928 _87932 f s)). Qed.
Lemma lem3385066 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term88 _87928 _87932 f s) = (term106 _87928 _87932 f s).
Proof. exact (EQ_MP (@lem3385065 _87928 _87932 f s) (@lem3385050 _87928 _87932 f s)). Qed.
Lemma lem3385067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3385068 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term90 _87928 _87932 f s) = (term107 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385067) (@lem3385066 _87928 _87932 f s)). Qed.
Lemma lem3385070 {A : Type'} (P : A -> Prop) (Q : Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3385071 {_87928 : Type'} (P : _87928 -> Prop) (Q : Prop) : (term108 _87928 P Q) = (term109 _87928 P Q).
Proof. exact (@lem3385070 _87928 P Q). Qed.
Lemma lem3385072 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term110 _87928 _87932 f s) = (term111 _87928 _87932 f s).
Proof. exact (@lem3385071 _87928 (term69 _87928 _87932 f s) (term30 _87932 s)). Qed.
Lemma lem3385073 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term112 _87928 _87932 f s x) = (term16 _87928 _87932 x f s).
Proof. exact (eq_refl (term112 _87928 _87932 f s x)). Qed.
Lemma lem3385074 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term113 _87928 _87932 f s) = (term69 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3385073 _87928 _87932 x f s)). Qed.
Lemma lem3385075 {_87928 : Type'} : (@ex _87928) = (@ex _87928).
Proof. exact (eq_refl (@ex _87928)). Qed.
Lemma lem3385076 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term114 _87928 _87932 f s) = (term70 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385075 _87928) (@lem3385074 _87928 _87932 f s)). Qed.
Lemma lem3385077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385078 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term115 _87928 _87932 f s) = (term82 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385077) (@lem3385076 _87928 _87932 f s)). Qed.
Lemma lem3385079 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (eq_refl (term30 _87932 s)). Qed.
Lemma lem3385080 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term110 _87928 _87932 f s) = (term84 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385078 _87928 _87932 f s) (@lem3385079 _87932 s)). Qed.
Lemma lem3385081 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385082 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term116 _87928 _87932 f s) = (term117 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385081) (@lem3385080 _87928 _87932 f s)). Qed.
Lemma lem3385083 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term112 _87928 _87932 f s x) = (term16 _87928 _87932 x f s).
Proof. exact (eq_refl (term112 _87928 _87932 f s x)). Qed.
Lemma lem3385084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385085 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term118 _87928 _87932 f s x) = (term119 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385084) (@lem3385083 _87928 _87932 x f s)). Qed.
Lemma lem3385086 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (eq_refl (term30 _87932 s)). Qed.
Lemma lem3385087 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term120 _87928 _87932 f x s) = (term121 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385085 _87928 _87932 x f s) (@lem3385086 _87932 s)). Qed.
Lemma lem3385088 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term122 _87928 _87932 f s) = (term123 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3385087 _87928 _87932 x f s)). Qed.
Lemma lem3385089 {_87928 : Type'} : (@ex _87928) = (@ex _87928).
Proof. exact (eq_refl (@ex _87928)). Qed.
Lemma lem3385090 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term111 _87928 _87932 f s) = (term124 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385089 _87928) (@lem3385088 _87928 _87932 f s)). Qed.
Lemma lem3385091 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term110 _87928 _87932 f s) = (term111 _87928 _87932 f s)) = ((term84 _87928 _87932 f s) = (term124 _87928 _87932 f s)).
Proof. exact (MK_COMB (@lem3385082 _87928 _87932 f s) (@lem3385090 _87928 _87932 f s)). Qed.
Lemma lem3385092 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term84 _87928 _87932 f s) = (term124 _87928 _87932 f s).
Proof. exact (EQ_MP (@lem3385091 _87928 _87932 f s) (@lem3385072 _87928 _87932 f s)). Qed.
Lemma lem3385094 {A : Type'} (P : A -> Prop) (Q : Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3385095 {_87932 : Type'} (P : _87932 -> Prop) (Q : Prop) : (term108 _87932 P Q) = (term109 _87932 P Q).
Proof. exact (@lem3385094 _87932 P Q). Qed.
Lemma lem3385096 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term125 _87928 _87932 x f s) = (term126 _87928 _87932 x f s).
Proof. exact (@lem3385095 _87932 (term48 _87928 _87932 x f s) (term30 _87932 s)). Qed.
Lemma lem3385097 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term56 _87928 _87932 x f s x') = (term47 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term56 _87928 _87932 x f s x')). Qed.
Lemma lem3385098 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term127 _87928 _87932 x f s) = (term48 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3385097 _87928 _87932 x f x' s)). Qed.
Lemma lem3385099 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385100 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term128 _87928 _87932 x f s) = (term16 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385099 _87932) (@lem3385098 _87928 _87932 x f s)). Qed.
Lemma lem3385101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385102 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term129 _87928 _87932 x f s) = (term119 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385101) (@lem3385100 _87928 _87932 x f s)). Qed.
Lemma lem3385103 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (eq_refl (term30 _87932 s)). Qed.
Lemma lem3385104 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term125 _87928 _87932 x f s) = (term121 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385102 _87928 _87932 x f s) (@lem3385103 _87932 s)). Qed.
Lemma lem3385105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385106 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term130 _87928 _87932 x f s) = (term131 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385105) (@lem3385104 _87928 _87932 x f s)). Qed.
Lemma lem3385107 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term56 _87928 _87932 x f s x') = (term47 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term56 _87928 _87932 x f s x')). Qed.
Lemma lem3385108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385109 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term132 _87928 _87932 x f s x') = (term133 _87928 _87932 x f x' s).
Proof. exact (MK_COMB (@lem3385108) (@lem3385107 _87928 _87932 x f x' s)). Qed.
Lemma lem3385110 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (eq_refl (term30 _87932 s)). Qed.
Lemma lem3385111 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term134 _87928 _87932 x f x' s) = (term135 _87928 _87932 x f x' s).
Proof. exact (MK_COMB (@lem3385109 _87928 _87932 x f x' s) (@lem3385110 _87932 s)). Qed.
Lemma lem3385112 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term136 _87928 _87932 x f s) = (term137 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3385111 _87928 _87932 x f x' s)). Qed.
Lemma lem3385113 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385114 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term126 _87928 _87932 x f s) = (term138 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385113 _87932) (@lem3385112 _87928 _87932 x f s)). Qed.
Lemma lem3385115 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term125 _87928 _87932 x f s) = (term126 _87928 _87932 x f s)) = ((term121 _87928 _87932 x f s) = (term138 _87928 _87932 x f s)).
Proof. exact (MK_COMB (@lem3385106 _87928 _87932 x f s) (@lem3385114 _87928 _87932 x f s)). Qed.
Lemma lem3385116 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term121 _87928 _87932 x f s) = (term138 _87928 _87932 x f s).
Proof. exact (EQ_MP (@lem3385115 _87928 _87932 x f s) (@lem3385096 _87928 _87932 x f s)). Qed.
Lemma lem3385117 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term123 _87928 _87932 f s) = (term139 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3385116 _87928 _87932 x f s)). Qed.
Lemma lem3385118 {_87928 : Type'} : (@ex _87928) = (@ex _87928).
Proof. exact (eq_refl (@ex _87928)). Qed.
Lemma lem3385119 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term124 _87928 _87932 f s) = (term140 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385118 _87928) (@lem3385117 _87928 _87932 f s)). Qed.
Lemma lem3385120 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term84 _87928 _87932 f s) = (term140 _87928 _87932 f s).
Proof. exact (TRANS (@lem3385092 _87928 _87932 f s) (@lem3385119 _87928 _87932 f s)). Qed.
Lemma lem3385121 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term92 _87928 _87932 f s) = (term141 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385068 _87928 _87932 f s) (@lem3385120 _87928 _87932 f s)). Qed.
Lemma lem3385125 {A : Type'} (P : A -> Prop) (Q : Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3385126 {_87932 : Type'} (P : _87932 -> Prop) (Q : Prop) : (term142 _87932 P Q) = (term143 _87932 P Q).
Proof. exact (@lem3385125 _87932 P Q). Qed.
Lemma lem3385127 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term144 _87928 _87932 f s) = (term145 _87928 _87932 f s).
Proof. exact (@lem3385126 _87932 (term105 _87928 _87932 f s) (term140 _87928 _87932 f s)). Qed.
Lemma lem3385128 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term146 _87928 _87932 f s x) = (term103 _87928 _87932 f x s).
Proof. exact (eq_refl (term146 _87928 _87932 f s x)). Qed.
Lemma lem3385129 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term147 _87928 _87932 f s) = (term105 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87932 => @lem3385128 _87928 _87932 f x s)). Qed.
Lemma lem3385130 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385131 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term148 _87928 _87932 f s) = (term106 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385130 _87932) (@lem3385129 _87928 _87932 f s)). Qed.
Lemma lem3385132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3385133 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term149 _87928 _87932 f s) = (term107 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385132) (@lem3385131 _87928 _87932 f s)). Qed.
Lemma lem3385134 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term140 _87928 _87932 f s) = (term140 _87928 _87932 f s).
Proof. exact (eq_refl (term140 _87928 _87932 f s)). Qed.
Lemma lem3385135 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term144 _87928 _87932 f s) = (term141 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385133 _87928 _87932 f s) (@lem3385134 _87928 _87932 f s)). Qed.
Lemma lem3385136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385137 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term150 _87928 _87932 f s) = (term151 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385136) (@lem3385135 _87928 _87932 f s)). Qed.
Lemma lem3385138 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term146 _87928 _87932 f s x) = (term103 _87928 _87932 f x s).
Proof. exact (eq_refl (term146 _87928 _87932 f s x)). Qed.
Lemma lem3385139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3385140 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term152 _87928 _87932 f s x) = (term153 _87928 _87932 f x s).
Proof. exact (MK_COMB (@lem3385139) (@lem3385138 _87928 _87932 f x s)). Qed.
Lemma lem3385141 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term140 _87928 _87932 f s) = (term140 _87928 _87932 f s).
Proof. exact (eq_refl (term140 _87928 _87932 f s)). Qed.
Lemma lem3385142 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term154 _87928 _87932 x f s) = (term155 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385140 _87928 _87932 f x s) (@lem3385141 _87928 _87932 f s)). Qed.
Lemma lem3385143 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term156 _87928 _87932 f s) = (term157 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87932 => @lem3385142 _87928 _87932 x f s)). Qed.
Lemma lem3385144 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385145 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term145 _87928 _87932 f s) = (term158 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385144 _87932) (@lem3385143 _87928 _87932 f s)). Qed.
Lemma lem3385146 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term144 _87928 _87932 f s) = (term145 _87928 _87932 f s)) = ((term141 _87928 _87932 f s) = (term158 _87928 _87932 f s)).
Proof. exact (MK_COMB (@lem3385137 _87928 _87932 f s) (@lem3385145 _87928 _87932 f s)). Qed.
Lemma lem3385147 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term141 _87928 _87932 f s) = (term158 _87928 _87932 f s).
Proof. exact (EQ_MP (@lem3385146 _87928 _87932 f s) (@lem3385127 _87928 _87932 f s)). Qed.
Lemma lem3385149 {A : Type'} (P : Prop) (Q : A -> Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3385150 {_87928 : Type'} (P : Prop) (Q : _87928 -> Prop) : (term159 _87928 P Q) = (term160 _87928 P Q).
Proof. exact (@lem3385149 _87928 P Q). Qed.
Lemma lem3385151 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term161 _87928 _87932 x f s) = (term162 _87928 _87932 x f s).
Proof. exact (@lem3385150 _87928 (term103 _87928 _87932 f x s) (term139 _87928 _87932 f s)). Qed.
Lemma lem3385152 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term163 _87928 _87932 f s x) = (term138 _87928 _87932 x f s).
Proof. exact (eq_refl (term163 _87928 _87932 f s x)). Qed.
Lemma lem3385153 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term164 _87928 _87932 f s) = (term139 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3385152 _87928 _87932 x f s)). Qed.
Lemma lem3385154 {_87928 : Type'} : (@ex _87928) = (@ex _87928).
Proof. exact (eq_refl (@ex _87928)). Qed.
Lemma lem3385155 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term165 _87928 _87932 f s) = (term140 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385154 _87928) (@lem3385153 _87928 _87932 f s)). Qed.
Lemma lem3385156 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term153 _87928 _87932 f x s) = (term153 _87928 _87932 f x s).
Proof. exact (eq_refl (term153 _87928 _87932 f x s)). Qed.
Lemma lem3385157 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term161 _87928 _87932 x f s) = (term155 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385156 _87928 _87932 f x s) (@lem3385155 _87928 _87932 f s)). Qed.
Lemma lem3385158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385159 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term166 _87928 _87932 x f s) = (term167 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385158) (@lem3385157 _87928 _87932 x f s)). Qed.
Lemma lem3385160 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term163 _87928 _87932 f s x) = (term138 _87928 _87932 x f s).
Proof. exact (eq_refl (term163 _87928 _87932 f s x)). Qed.
Lemma lem3385161 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term153 _87928 _87932 f x s) = (term153 _87928 _87932 f x s).
Proof. exact (eq_refl (term153 _87928 _87932 f x s)). Qed.
Lemma lem3385162 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term168 _87928 _87932 x f s x') = (term169 _87928 _87932 x x' f s).
Proof. exact (MK_COMB (@lem3385161 _87928 _87932 f x s) (@lem3385160 _87928 _87932 x' f s)). Qed.
Lemma lem3385163 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term170 _87928 _87932 x f s) = (term171 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87928 => @lem3385162 _87928 _87932 x x' f s)). Qed.
Lemma lem3385164 {_87928 : Type'} : (@ex _87928) = (@ex _87928).
Proof. exact (eq_refl (@ex _87928)). Qed.
Lemma lem3385165 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term162 _87928 _87932 x f s) = (term172 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385164 _87928) (@lem3385163 _87928 _87932 x f s)). Qed.
Lemma lem3385166 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term161 _87928 _87932 x f s) = (term162 _87928 _87932 x f s)) = ((term155 _87928 _87932 x f s) = (term172 _87928 _87932 x f s)).
Proof. exact (MK_COMB (@lem3385159 _87928 _87932 x f s) (@lem3385165 _87928 _87932 x f s)). Qed.
Lemma lem3385167 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term155 _87928 _87932 x f s) = (term172 _87928 _87932 x f s).
Proof. exact (EQ_MP (@lem3385166 _87928 _87932 x f s) (@lem3385151 _87928 _87932 x f s)). Qed.
Lemma lem3385169 {A : Type'} (P : Prop) (Q : A -> Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3385170 {_87932 : Type'} (P : Prop) (Q : _87932 -> Prop) : (term159 _87932 P Q) = (term160 _87932 P Q).
Proof. exact (@lem3385169 _87932 P Q). Qed.
Lemma lem3385171 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term173 _87928 _87932 x x' f s) = (term174 _87928 _87932 x x' f s).
Proof. exact (@lem3385170 _87932 (term103 _87928 _87932 f x s) (term137 _87928 _87932 x' f s)). Qed.
Lemma lem3385172 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term175 _87928 _87932 x f s x') = (term135 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term175 _87928 _87932 x f s x')). Qed.
Lemma lem3385173 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term176 _87928 _87932 x f s) = (term137 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3385172 _87928 _87932 x f x' s)). Qed.
Lemma lem3385174 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385175 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term177 _87928 _87932 x f s) = (term138 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385174 _87932) (@lem3385173 _87928 _87932 x f s)). Qed.
Lemma lem3385176 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term153 _87928 _87932 f x s) = (term153 _87928 _87932 f x s).
Proof. exact (eq_refl (term153 _87928 _87932 f x s)). Qed.
Lemma lem3385177 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term173 _87928 _87932 x x' f s) = (term169 _87928 _87932 x x' f s).
Proof. exact (MK_COMB (@lem3385176 _87928 _87932 f x s) (@lem3385175 _87928 _87932 x' f s)). Qed.
Lemma lem3385178 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3385179 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term178 _87928 _87932 x x' f s) = (term179 _87928 _87932 x x' f s).
Proof. exact (MK_COMB (@lem3385178) (@lem3385177 _87928 _87932 x x' f s)). Qed.
Lemma lem3385180 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term175 _87928 _87932 x f s x') = (term135 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term175 _87928 _87932 x f s x')). Qed.
Lemma lem3385181 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term153 _87928 _87932 f x s) = (term153 _87928 _87932 f x s).
Proof. exact (eq_refl (term153 _87928 _87932 f x s)). Qed.
Lemma lem3385182 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) : (term180 _87928 _87932 x x' f s x'') = (term181 _87928 _87932 x x' f x'' s).
Proof. exact (MK_COMB (@lem3385181 _87928 _87932 f x s) (@lem3385180 _87928 _87932 x' f x'' s)). Qed.
Lemma lem3385183 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term182 _87928 _87932 x x' f s) = (term183 _87928 _87932 x x' f s).
Proof. exact (fun_ext (fun x'' : _87932 => @lem3385182 _87928 _87932 x x' f x'' s)). Qed.
Lemma lem3385184 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385185 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term174 _87928 _87932 x x' f s) = (term184 _87928 _87932 x x' f s).
Proof. exact (MK_COMB (@lem3385184 _87932) (@lem3385183 _87928 _87932 x x' f s)). Qed.
Lemma lem3385186 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : ((term173 _87928 _87932 x x' f s) = (term174 _87928 _87932 x x' f s)) = ((term169 _87928 _87932 x x' f s) = (term184 _87928 _87932 x x' f s)).
Proof. exact (MK_COMB (@lem3385179 _87928 _87932 x x' f s) (@lem3385185 _87928 _87932 x x' f s)). Qed.
Lemma lem3385187 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term169 _87928 _87932 x x' f s) = (term184 _87928 _87932 x x' f s).
Proof. exact (EQ_MP (@lem3385186 _87928 _87932 x x' f s) (@lem3385171 _87928 _87932 x x' f s)). Qed.
Lemma lem3385188 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term171 _87928 _87932 x f s) = (term185 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87928 => @lem3385187 _87928 _87932 x x' f s)). Qed.
Lemma lem3385189 {_87928 : Type'} : (@ex _87928) = (@ex _87928).
Proof. exact (eq_refl (@ex _87928)). Qed.
Lemma lem3385190 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term172 _87928 _87932 x f s) = (term186 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385189 _87928) (@lem3385188 _87928 _87932 x f s)). Qed.
Lemma lem3385191 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term155 _87928 _87932 x f s) = (term186 _87928 _87932 x f s).
Proof. exact (TRANS (@lem3385167 _87928 _87932 x f s) (@lem3385190 _87928 _87932 x f s)). Qed.
Lemma lem3385192 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term157 _87928 _87932 f s) = (term187 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87932 => @lem3385191 _87928 _87932 x f s)). Qed.
Lemma lem3385193 {_87932 : Type'} : (@ex _87932) = (@ex _87932).
Proof. exact (eq_refl (@ex _87932)). Qed.
Lemma lem3385194 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term158 _87928 _87932 f s) = (term188 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385193 _87932) (@lem3385192 _87928 _87932 f s)). Qed.
Lemma lem3385195 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term141 _87928 _87932 f s) = (term188 _87928 _87932 f s).
Proof. exact (TRANS (@lem3385147 _87928 _87932 f s) (@lem3385194 _87928 _87932 f s)). Qed.
Lemma lem3385197 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term92 _87928 _87932 f s) = (term188 _87928 _87932 f s).
Proof. exact (TRANS (@lem3385121 _87928 _87932 f s) (@lem3385195 _87928 _87932 f s)). Qed.
Lemma lem3385198 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term50 _87928 _87932 f s) = (term188 _87928 _87932 f s).
Proof. exact (TRANS (@lem3384933 _87928 _87932 f s) (@lem3385197 _87928 _87932 f s)). Qed.
Lemma lem3385199 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term50 _87928 _87932 f s) : term188 _87928 _87932 f s.
Proof. exact (EQ_MP (@lem3385198 _87928 _87932 f s) (@lem3384865 _87928 _87932 f s h1)). Qed.
Lemma lem3385200 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term186 _87928 _87932 x f s) : term186 _87928 _87932 x f s.
Proof. exact (h1). Qed.
Lemma lem3385201 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term184 _87928 _87932 x x' f s) : term184 _87928 _87932 x x' f s.
Proof. exact (h1). Qed.
Lemma lem3385202 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term181 _87928 _87932 x x' f x'' s) : term181 _87928 _87932 x x' f x'' s.
Proof. exact (h1). Qed.
Lemma lem3385209 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term27 _87932 x s) = (term27 _87932 x s).
Proof. exact (eq_refl (term27 _87932 x s)). Qed.
Lemma lem3385210 {_87932 : Type'} (s : _87932 -> Prop) : (term29 _87932 s) = (term29 _87932 s).
Proof. exact (fun_ext (fun x : _87932 => @lem3385209 _87932 x s)). Qed.
Lemma lem3385211 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3385212 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (MK_COMB (@lem3385211 _87932) (@lem3385210 _87932 s)). Qed.
Lemma lem3385229 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) : (term133 _87928 _87932 x' f x'' s) = (term133 _87928 _87932 x' f x'' s).
Proof. exact (eq_refl (term133 _87928 _87932 x' f x'' s)). Qed.
Lemma lem3385230 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) : (term135 _87928 _87932 x' f x'' s) = (term135 _87928 _87932 x' f x'' s).
Proof. exact (MK_COMB (@lem3385229 _87928 _87932 x' f x'' s) (@lem3385212 _87932 s)). Qed.
Lemma lem3385235 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (@IN _87932 x s) = (@IN _87932 x s).
Proof. exact (eq_refl (@IN _87932 x s)). Qed.
Lemma lem3385254 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term52 _87928 _87932 x f x' s) = (term52 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term52 _87928 _87932 x f x' s)). Qed.
Lemma lem3385255 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term59 _87928 _87932 x f s) = (term59 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3385254 _87928 _87932 x f x' s)). Qed.
Lemma lem3385256 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3385257 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term60 _87928 _87932 x f s) = (term60 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385256 _87932) (@lem3385255 _87928 _87932 x f s)). Qed.
Lemma lem3385258 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term71 _87928 _87932 f s) = (term71 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3385257 _87928 _87932 x f s)). Qed.
Lemma lem3385259 {_87928 : Type'} : (@all _87928) = (@all _87928).
Proof. exact (eq_refl (@all _87928)). Qed.
Lemma lem3385260 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term72 _87928 _87932 f s) = (term72 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385259 _87928) (@lem3385258 _87928 _87932 f s)). Qed.
Lemma lem3385261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3385262 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term86 _87928 _87932 f s) = (term86 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385261) (@lem3385260 _87928 _87932 f s)). Qed.
Lemma lem3385263 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term103 _87928 _87932 f x s) = (term103 _87928 _87932 f x s).
Proof. exact (MK_COMB (@lem3385262 _87928 _87932 f s) (@lem3385235 _87932 x s)). Qed.
Lemma lem3385264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3385265 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) : (term153 _87928 _87932 f x s) = (term153 _87928 _87932 f x s).
Proof. exact (MK_COMB (@lem3385264) (@lem3385263 _87928 _87932 f x s)). Qed.
Lemma lem3385266 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) : (term181 _87928 _87932 x x' f x'' s) = (term181 _87928 _87932 x x' f x'' s).
Proof. exact (MK_COMB (@lem3385265 _87928 _87932 f x s) (@lem3385230 _87928 _87932 x' f x'' s)). Qed.
Lemma lem3385267 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term181 _87928 _87932 x x' f x'' s) : term181 _87928 _87932 x x' f x'' s.
Proof. exact (EQ_MP (@lem3385266 _87928 _87932 x x' f x'' s) (@lem3385202 _87928 _87932 x x' f x'' s h1)). Qed.
Lemma lem3385268 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term103 _87928 _87932 f x s.
Proof. exact (h1). Qed.
Lemma lem3385269 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term135 _87928 _87932 x' f x'' s.
Proof. exact (h1). Qed.
Lemma lem3385271 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term72 _87928 _87932 f s.
Proof. exact (proj1 (@lem3385268 _87928 _87932 f x s h1)). Qed.
Lemma lem3385272 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term30 _87932 s.
Proof. exact (proj2 (@lem3385269 _87928 _87932 x' f x'' s h1)). Qed.
Lemma lem3385273 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term47 _87928 _87932 x' f x'' s.
Proof. exact (proj1 (@lem3385269 _87928 _87932 x' f x'' s h1)). Qed.
Lemma lem3385283 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (x' : _87932) (s : _87932 -> Prop) : (term52 _87928 _87932 x f x' s) = (term52 _87928 _87932 x f x' s).
Proof. exact (eq_refl (term52 _87928 _87932 x f x' s)). Qed.
Lemma lem3385284 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term59 _87928 _87932 x f s) = (term59 _87928 _87932 x f s).
Proof. exact (fun_ext (fun x' : _87932 => @lem3385283 _87928 _87932 x f x' s)). Qed.
Lemma lem3385285 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3385286 {_87928 _87932 : Type'} (x : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term60 _87928 _87932 x f s) = (term60 _87928 _87932 x f s).
Proof. exact (MK_COMB (@lem3385285 _87932) (@lem3385284 _87928 _87932 x f s)). Qed.
Lemma lem3385287 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term71 _87928 _87932 f s) = (term71 _87928 _87932 f s).
Proof. exact (fun_ext (fun x : _87928 => @lem3385286 _87928 _87932 x f s)). Qed.
Lemma lem3385288 {_87928 : Type'} : (@all _87928) = (@all _87928).
Proof. exact (eq_refl (@all _87928)). Qed.
Lemma lem3385290 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term72 _87928 _87932 f s) = (term72 _87928 _87932 f s).
Proof. exact (MK_COMB (@lem3385288 _87928) (@lem3385287 _87928 _87932 f s)). Qed.
Lemma lem3385291 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term72 _87928 _87932 f s.
Proof. exact (EQ_MP (@lem3385290 _87928 _87932 f s) (@lem3385271 _87928 _87932 f x s h1)). Qed.
Lemma lem3385297 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term27 _87932 x s) = (term27 _87932 x s).
Proof. exact (eq_refl (term27 _87932 x s)). Qed.
Lemma lem3385298 {_87932 : Type'} (s : _87932 -> Prop) : (term29 _87932 s) = (term29 _87932 s).
Proof. exact (fun_ext (fun x : _87932 => @lem3385297 _87932 x s)). Qed.
Lemma lem3385299 {_87932 : Type'} : (@all _87932) = (@all _87932).
Proof. exact (eq_refl (@all _87932)). Qed.
Lemma lem3385301 {_87932 : Type'} (s : _87932 -> Prop) : (term30 _87932 s) = (term30 _87932 s).
Proof. exact (MK_COMB (@lem3385299 _87932) (@lem3385298 _87932 s)). Qed.
Lemma lem3385302 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term30 _87932 s.
Proof. exact (EQ_MP (@lem3385301 _87932 s) (@lem3385272 _87928 _87932 x' f x'' s h1)). Qed.
Lemma lem3385311 {_87928 _87932 : Type'} (_35549 : _87928) (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term189 _87928 _87932 f s _35549.
Proof. exact (@lem3385291 _87928 _87932 f x s h1 _35549). Qed.
Lemma lem3385312 {_87928 _87932 : Type'} (_35549 : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) : (term189 _87928 _87932 f s _35549) = (term60 _87928 _87932 _35549 f s).
Proof. exact (eq_refl (term189 _87928 _87932 f s _35549)). Qed.
Lemma lem3385313 {_87928 _87932 : Type'} (_35549 : _87928) (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term60 _87928 _87932 _35549 f s.
Proof. exact (EQ_MP (@lem3385312 _87928 _87932 _35549 f s) (@lem3385311 _87928 _87932 _35549 f x s h1)). Qed.
Lemma lem3385314 {_87928 _87932 : Type'} (_35549 : _87928) (_35550 : _87932) (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term190 _87928 _87932 _35549 f s _35550.
Proof. exact (@lem3385313 _87928 _87932 _35549 f x s h1 _35550). Qed.
Lemma lem3385315 {_87928 _87932 : Type'} (_35549 : _87928) (f : _87932 -> _87928) (_35550 : _87932) (s : _87932 -> Prop) : (term190 _87928 _87932 _35549 f s _35550) = (term52 _87928 _87932 _35549 f _35550 s).
Proof. exact (eq_refl (term190 _87928 _87932 _35549 f s _35550)). Qed.
Lemma lem3385317 {_87928 _87932 : Type'} (_35551 : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term76 _87932 s _35551.
Proof. exact (@lem3385302 _87928 _87932 x' f x'' s h1 _35551). Qed.
Lemma lem3385318 {_87932 : Type'} (_35551 : _87932) (s : _87932 -> Prop) : (term76 _87932 s _35551) = (term27 _87932 _35551 s).
Proof. exact (eq_refl (term76 _87932 s _35551)). Qed.
Lemma lem3385325 {_87928 _87932 : Type'} (_35549 : _87928) (_35550 : _87932) (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term52 _87928 _87932 _35549 f _35550 s.
Proof. exact (EQ_MP (@lem3385315 _87928 _87932 _35549 f _35550 s) (@lem3385314 _87928 _87932 _35549 _35550 f x s h1)). Qed.
Lemma lem3385361 {_87928 _87932 : Type'} (_35551 : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term27 _87932 _35551 s.
Proof. exact (EQ_MP (@lem3385318 _87932 _35551 s) (@lem3385317 _87928 _87932 _35551 x' f x'' s h1)). Qed.
Lemma lem3385410 {_87928 : Type'} (x : _87928) : x = x.
Proof. exact (@lem21386 _87928 x). Qed.
Lemma lem3385411 {_87928 : Type'} (x : _87928) : x = x.
Proof. exact (@lem3385410 _87928 x). Qed.
Lemma lem3385412 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) : (f x) = (f x).
Proof. exact (@lem3385411 _87928 (f x)). Qed.
Lemma lem3385413 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) : term191 _87928 _87932 f x.
Proof. exact (fun h0 : term192 _87928 _87932 f x => @lem3385412 _87928 _87932 f x). Qed.
Lemma lem3385415 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3385416 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) : (term191 _87928 _87932 f x) = ((f x) = (f x)).
Proof. exact (@lem3385415 ((f x) = (f x))). Qed.
Lemma lem3385417 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) : (f x) = (f x).
Proof. exact (EQ_MP (@lem3385416 _87928 _87932 f x) (@lem3385413 _87928 _87932 f x)). Qed.
Lemma lem3385419 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : @IN _87932 x s.
Proof. exact (proj2 (@lem3385268 _87928 _87932 f x s h1)). Qed.
Lemma lem3385420 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term194 _87932 x s.
Proof. exact (fun h0 : term27 _87932 x s => @lem3385419 _87928 _87932 f x s h1). Qed.
Lemma lem3385422 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3385423 {_87932 : Type'} (x : _87932) (s : _87932 -> Prop) : (term194 _87932 x s) = (@IN _87932 x s).
Proof. exact (@lem3385422 (@IN _87932 x s)). Qed.
Lemma lem3385424 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : @IN _87932 x s.
Proof. exact (EQ_MP (@lem3385423 _87932 x s) (@lem3385420 _87928 _87932 f x s h1)). Qed.
Lemma lem3385426 (a : Prop) (b : Prop) : (term195 a b) = (term196 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3385427 {_87928 _87932 : Type'} (_35549 : _87928) (f : _87932 -> _87928) (_35550 : _87932) (s : _87932 -> Prop) : (term52 _87928 _87932 _35549 f _35550 s) = (term51 _87928 _87932 _35549 f _35550 s).
Proof. exact (@lem3385426 (_35549 = (f _35550)) (@IN _87932 _35550 s)). Qed.
Lemma lem3385429 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3385430 {_87928 _87932 : Type'} (_35549 : _87928) (f : _87932 -> _87928) (_35550 : _87932) (s : _87932 -> Prop) : (term51 _87928 _87932 _35549 f _35550 s) = (term197 _87928 _87932 _35549 f _35550 s).
Proof. exact (@lem3385429 (term47 _87928 _87932 _35549 f _35550 s)). Qed.
Lemma lem3385431 {_87928 _87932 : Type'} (_35549 : _87928) (f : _87932 -> _87928) (_35550 : _87932) (s : _87932 -> Prop) : (term52 _87928 _87932 _35549 f _35550 s) = (term197 _87928 _87932 _35549 f _35550 s).
Proof. exact (TRANS (@lem3385427 _87928 _87932 _35549 f _35550 s) (@lem3385430 _87928 _87932 _35549 f _35550 s)). Qed.
Lemma lem3385433 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term198 _87928 _87932 f x s.
Proof. exact (conj (@lem3385417 _87928 _87932 f x) (@lem3385424 _87928 _87932 f x s h1)). Qed.
Lemma lem3385435 {_87928 _87932 : Type'} (_35549 : _87928) (_35550 : _87932) (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term197 _87928 _87932 _35549 f _35550 s.
Proof. exact (EQ_MP (@lem3385431 _87928 _87932 _35549 f _35550 s) (@lem3385325 _87928 _87932 _35549 _35550 f x s h1)). Qed.
Lemma lem3385436 {_87928 _87932 : Type'} (_35549 : _87928) (_35550 : _87932) (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term197 _87928 _87932 _35549 f _35550 s.
Proof. exact (@lem3385435 _87928 _87932 _35549 _35550 f x s h1). Qed.
Lemma lem3385437 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term199 _87928 _87932 f x s.
Proof. exact (@lem3385436 _87928 _87932 (f x) x f x s h1). Qed.
Lemma lem3385440 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : False.
Proof. exact (@lem3385437 _87928 _87932 f x s h1 (@lem3385433 _87928 _87932 f x s h1)). Qed.
Lemma lem3385441 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : term200.
Proof. exact (fun h0 : ~ False => @lem3385440 _87928 _87932 f x s h1). Qed.
Lemma lem3385443 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3385444 : term200 = False.
Proof. exact (@lem3385443 False). Qed.
Lemma lem3385445 {_87928 _87932 : Type'} (f : _87932 -> _87928) (x : _87932) (s : _87932 -> Prop) (h1 : term103 _87928 _87932 f x s) : False.
Proof. exact (EQ_MP (@lem3385444) (@lem3385441 _87928 _87932 f x s h1)). Qed.
Lemma lem3385447 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : @IN _87932 x'' s.
Proof. exact (proj2 (@lem3385273 _87928 _87932 x' f x'' s h1)). Qed.
Lemma lem3385448 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term194 _87932 x'' s.
Proof. exact (fun h0 : term27 _87932 x'' s => @lem3385447 _87928 _87932 x' f x'' s h1). Qed.
Lemma lem3385450 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3385451 {_87932 : Type'} (x'' : _87932) (s : _87932 -> Prop) : (term194 _87932 x'' s) = (@IN _87932 x'' s).
Proof. exact (@lem3385450 (@IN _87932 x'' s)). Qed.
Lemma lem3385452 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : @IN _87932 x'' s.
Proof. exact (EQ_MP (@lem3385451 _87932 x'' s) (@lem3385448 _87928 _87932 x' f x'' s h1)). Qed.
Lemma lem3385455 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3385457 {_87932 : Type'} (_35551 : _87932) (s : _87932 -> Prop) : (term27 _87932 _35551 s) = (term201 _87932 _35551 s).
Proof. exact (@lem3385455 (@IN _87932 _35551 s)). Qed.
Lemma lem3385460 {_87928 _87932 : Type'} (_35551 : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term201 _87932 _35551 s.
Proof. exact (EQ_MP (@lem3385457 _87932 _35551 s) (@lem3385361 _87928 _87932 _35551 x' f x'' s h1)). Qed.
Lemma lem3385461 {_87928 _87932 : Type'} (_35551 : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term201 _87932 _35551 s.
Proof. exact (@lem3385460 _87928 _87932 _35551 x' f x'' s h1). Qed.
Lemma lem3385462 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term201 _87932 x'' s.
Proof. exact (@lem3385461 _87928 _87932 x'' x' f x'' s h1). Qed.
Lemma lem3385465 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : False.
Proof. exact (@lem3385462 _87928 _87932 x' f x'' s h1 (@lem3385452 _87928 _87932 x' f x'' s h1)). Qed.
Lemma lem3385466 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : term200.
Proof. exact (fun h0 : ~ False => @lem3385465 _87928 _87932 x' f x'' s h1). Qed.
Lemma lem3385468 (p : Prop) : (term193 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3385469 : term200 = False.
Proof. exact (@lem3385468 False). Qed.
Lemma lem3385471 {_87928 _87932 : Type'} (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term135 _87928 _87932 x' f x'' s) : False.
Proof. exact (EQ_MP (@lem3385469) (@lem3385466 _87928 _87932 x' f x'' s h1)). Qed.
Lemma lem3385472 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term181 _87928 _87932 x x' f x'' s) : False.
Proof. exact (or_elim (@lem3385267 _87928 _87932 x x' f x'' s h1) (fun h0 : term103 _87928 _87932 f x s => @lem3385445 _87928 _87932 f x s h0) (fun h0 : term135 _87928 _87932 x' f x'' s => @lem3385471 _87928 _87932 x' f x'' s h0)). Qed.
Lemma lem3385473 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term181 _87928 _87932 x x' f x'' s) : (term181 _87928 _87932 x x' f x'' s) = False.
Proof. exact (prop_ext (fun h2 : term181 _87928 _87932 x x' f x'' s => @lem3385472 _87928 _87932 x x' f x'' s h1) (fun h2 : False => @lem3385267 _87928 _87932 x x' f x'' s h1)). Qed.
Lemma lem3385474 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (x'' : _87932) (s : _87932 -> Prop) (h1 : term181 _87928 _87932 x x' f x'' s) : False.
Proof. exact (EQ_MP (@lem3385473 _87928 _87932 x x' f x'' s h1) (@lem3385267 _87928 _87932 x x' f x'' s h1)). Qed.
Lemma lem3385475 {_87928 _87932 : Type'} (x : _87932) (x' : _87928) (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term184 _87928 _87932 x x' f s) : False.
Proof. exact (ex_elim (@lem3385201 _87928 _87932 x x' f s h1) (fun x'' : _87932 => fun h0 : term183 _87928 _87932 x x' f s x'' => @lem3385474 _87928 _87932 x x' f x'' s h0)). Qed.
Lemma lem3385476 {_87928 _87932 : Type'} (x : _87932) (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term186 _87928 _87932 x f s) : False.
Proof. exact (ex_elim (@lem3385200 _87928 _87932 x f s h1) (fun x' : _87928 => fun h0 : term185 _87928 _87932 x f s x' => @lem3385475 _87928 _87932 x x' f s h0)). Qed.
Lemma lem3385477 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term50 _87928 _87932 f s) : False.
Proof. exact (ex_elim (@lem3385199 _87928 _87932 f s h1) (fun x : _87932 => fun h0 : term187 _87928 _87932 f s x => @lem3385476 _87928 _87932 x f s h0)). Qed.
Lemma lem3385478 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term50 _87928 _87932 f s) : (term50 _87928 _87932 f s) = False.
Proof. exact (prop_ext (fun h2 : term50 _87928 _87932 f s => @lem3385477 _87928 _87932 f s h1) (fun h2 : False => @lem3384865 _87928 _87932 f s h1)). Qed.
Lemma lem3385479 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) (h1 : term50 _87928 _87932 f s) : False.
Proof. exact (EQ_MP (@lem3385478 _87928 _87932 f s h1) (@lem3384865 _87928 _87932 f s h1)). Qed.
Lemma lem3385480 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : term49 _87928 _87932 f s.
Proof. exact (fun h0 : term50 _87928 _87932 f s => @lem3385479 _87928 _87932 f s h0). Qed.
Lemma lem3385481 {_87928 _87932 : Type'} (f : _87932 -> _87928) (s : _87932 -> Prop) : (term22 _87928 _87932 f s) = (term30 _87932 s).
Proof. exact (EQ_MP (@lem3384864 _87928 _87932 f s) (@lem3385480 _87928 _87932 f s)). Qed.
Lemma lem3385486 {_87928 _87932 : Type'} (f : _87932 -> _87928) : term34 _87928 _87932 f.
Proof. exact (fun s : _87932 -> Prop => @lem3385481 _87928 _87932 f s). Qed.
Lemma lem3385491 {_87928 _87932 : Type'} : term38 _87928 _87932.
Proof. exact (fun f : _87932 -> _87928 => @lem3385486 _87928 _87932 f). Qed.
Lemma lem3385492 {_87928 _87932 : Type'} : term40 _87928 _87932.
Proof. exact (EQ_MP (@lem3384860 _87928 _87932) (@lem3385491 _87928 _87932)). Qed.
Lemma lem3385494 {_87928 _87932 : Type'} : term40 _87928 _87932.
Proof. exact (@lem3384719 _87928 _87932 (@lem3385492 _87928 _87932)). Qed.
Lemma lem3385495 {_87928 _87932 : Type'} (h1 : term41 _87928 _87932) : False.
Proof. exact (@lem3385494 _87928 _87932 (@lem3384703 _87928 _87932 h1)). Qed.
Lemma lem3385496 {_87928 _87932 : Type'} (h1 : term41 _87928 _87932) : (term41 _87928 _87932) = False.
Proof. exact (prop_ext (fun h2 : term41 _87928 _87932 => @lem3385495 _87928 _87932 h1) (fun h2 : False => @lem3384703 _87928 _87932 h1)). Qed.
Lemma lem3385497 {_87928 _87932 : Type'} (h1 : term41 _87928 _87932) : False.
Proof. exact (EQ_MP (@lem3385496 _87928 _87932 h1) (@lem3384703 _87928 _87932 h1)). Qed.
Lemma lem3385498 {_87928 _87932 : Type'} : term40 _87928 _87932.
Proof. exact (fun h0 : term41 _87928 _87932 => @lem3385497 _87928 _87932 h0). Qed.
Lemma lem3385499 {_87928 _87932 : Type'} : term38 _87928 _87932.
Proof. exact (EQ_MP (@lem3384702 _87928 _87932) (@lem3385498 _87928 _87932)). Qed.
Lemma lem3385500 {_87928 _87932 : Type'} : term37 _87928 _87932.
Proof. exact (EQ_MP (@lem3384698 _87928 _87932) (@lem3385499 _87928 _87932)). Qed.
