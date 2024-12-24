Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_IMP_INJECTIVE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IMAGE_IMP_INJECTIVE_GEN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem4963589 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4963590 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4963591 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4963590 t1) (@lem4963589 t1)). Qed.
Lemma lem4963592 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4963591 t1 t2). Qed.
Lemma lem4963593 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4963594 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4963593 t1 t2) (@lem4963592 t1 t2)). Qed.
Lemma lem4963595 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4963594 t1 t2 t3). Qed.
Lemma lem4963596 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4963597 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4963596 t1 t2 t3) (@lem4963595 t1 t2 t3)). Qed.
Lemma lem4963598 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4963597 t1 t2 t3)). Qed.
Lemma lem4963600 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4963601 {_113204 : Type'} : (term8 _113204) = (term9 _113204).
Proof. exact (@lem4963600 (term8 _113204)). Qed.
Lemma lem4963602 {_113204 : Type'} : (term9 _113204) = (term8 _113204).
Proof. exact (SYM (@lem4963601 _113204)). Qed.
Lemma lem4963603 {_113204 : Type'} (h1 : term10 _113204) : term10 _113204.
Proof. exact (h1). Qed.
Lemma lem4963604 {_113204 B : Type'} : term11 _113204 B.
Proof. exact (@lem4963588 _113204 B). Qed.
Lemma lem4963605 {_113204 A : Type'} : term12 _113204 A.
Proof. exact (@lem4963588 A _113204). Qed.
Lemma lem4963606 {_113204 : Type'} : term13 _113204.
Proof. exact (@lem4963588 _113204 _113204). Qed.
Lemma lem4963608 {_113204 A : Type'} : term14 _113204 A.
Proof. exact (@lem4963588 A (_113204 -> Prop)). Qed.
Lemma lem4963610 {_113204 B : Type'} : term15 _113204 B.
Proof. exact (@lem4963588 (_113204 -> Prop) B). Qed.
Lemma lem4963614 {_113204 A B : Type'} (h1 : term16 _113204 A B) : term16 _113204 A B.
Proof. exact (h1). Qed.
Lemma lem4963615 {_113204 A B : Type'} : term17 _113204 A B.
Proof. exact (fun h0 : term16 _113204 A B => @lem4963614 _113204 A B h0). Qed.
Lemma lem4963616 {_113204 A B : Type'} (h1 : term17 _113204 A B) : term17 _113204 A B.
Proof. exact (h1). Qed.
Lemma lem4963617 {_113204 A B : Type'} (h1 : term16 _113204 A B) : term16 _113204 A B.
Proof. exact (h1). Qed.
Lemma lem4963618 {_113204 A B : Type'} (h1 : term16 _113204 A B) (h2 : term17 _113204 A B) : term16 _113204 A B.
Proof. exact (@lem4963616 _113204 A B h2 (@lem4963617 _113204 A B h1)). Qed.
Lemma lem4963619 {_113204 A B : Type'} (h1 : term16 _113204 A B) : term18 _113204 A B.
Proof. exact (fun h0 : term17 _113204 A B => @lem4963618 _113204 A B h1 h0). Qed.
Lemma lem4963620 {_113204 A B : Type'} (h1 : term17 _113204 A B) : term17 _113204 A B.
Proof. exact (h1). Qed.
Lemma lem4963621 {_113204 A B : Type'} (h1 : term16 _113204 A B) (h2 : term17 _113204 A B) : term16 _113204 A B.
Proof. exact (@lem4963619 _113204 A B h1 (@lem4963620 _113204 A B h2)). Qed.
Lemma lem4963622 {_113204 A B : Type'} (h1 : term17 _113204 A B) : term17 _113204 A B.
Proof. exact (fun h0 : term16 _113204 A B => @lem4963621 _113204 A B h0 h1). Qed.
Lemma lem4963623 {_113204 A B : Type'} : term19 _113204 A B.
Proof. exact (fun h0 : term17 _113204 A B => @lem4963622 _113204 A B h0). Qed.
Lemma lem4963626 {_113204 A B : Type'} : term17 _113204 A B.
Proof. exact (@lem4963623 _113204 A B (@lem4963615 _113204 A B)). Qed.
Lemma lem4963627 {_113204 A B : Type'} : term17 _113204 A B.
Proof. exact (@lem4963626 _113204 A B). Qed.
Lemma lem4963793 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4963794 {_113204 B : Type'} : (term20 _113204 B) = (term21 _113204 B).
Proof. exact (@lem4963793 (term15 _113204 B)). Qed.
Lemma lem4963827 {_113204 A : Type'} : (term22 _113204 A) = (term22 _113204 A).
Proof. exact (eq_refl (term22 _113204 A)). Qed.
Lemma lem4963828 {_113204 A B : Type'} : (term23 _113204 A B) = (term24 _113204 A B).
Proof. exact (MK_COMB (@lem4963827 _113204 A) (@lem4963794 _113204 B)). Qed.
Lemma lem4963831 {_113204 A : Type'} : (term25 _113204 A) = (term25 _113204 A).
Proof. exact (eq_refl (term25 _113204 A)). Qed.
Lemma lem4963832 {_113204 A B : Type'} : (term26 _113204 A B) = (term27 _113204 A B).
Proof. exact (MK_COMB (@lem4963831 _113204 A) (@lem4963828 _113204 A B)). Qed.
Lemma lem4963835 {_113204 B : Type'} : (term28 _113204 B) = (term28 _113204 B).
Proof. exact (eq_refl (term28 _113204 B)). Qed.
Lemma lem4963836 {_113204 A B : Type'} : (term29 _113204 A B) = (term30 _113204 A B).
Proof. exact (MK_COMB (@lem4963835 _113204 B) (@lem4963832 _113204 A B)). Qed.
Lemma lem4963839 {_113204 : Type'} : (term31 _113204) = (term31 _113204).
Proof. exact (eq_refl (term31 _113204)). Qed.
Lemma lem4963840 {_113204 A B : Type'} : (term32 _113204 A B) = (term33 _113204 A B).
Proof. exact (MK_COMB (@lem4963839 _113204) (@lem4963836 _113204 A B)). Qed.
Lemma lem4963843 {_113204 : Type'} : (term34 _113204) = (term34 _113204).
Proof. exact (eq_refl (term34 _113204)). Qed.
Lemma lem4963850 {_113204 A B : Type'} : (term16 _113204 A B) = (term35 _113204 A B).
Proof. exact (MK_COMB (@lem4963843 _113204) (@lem4963840 _113204 A B)). Qed.
Lemma lem4963863 {_113204 B : Type'} (s : type686 _113204) (f : type685 _113204 B) (x : _113204 -> Prop) (y : _113204 -> Prop) : (term36 _113204 B s f x y) = (term36 _113204 B s f x y).
Proof. exact (eq_refl (term36 _113204 B s f x y)). Qed.
Lemma lem4963864 {_113204 B : Type'} (s : type686 _113204) (f : type685 _113204 B) (x : _113204 -> Prop) : (term37 _113204 B s f x) = (term37 _113204 B s f x).
Proof. exact (fun_ext (fun y : _113204 -> Prop => @lem4963863 _113204 B s f x y)). Qed.
Lemma lem4963865 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4963866 {_113204 B : Type'} (s : type686 _113204) (f : type685 _113204 B) (x : _113204 -> Prop) : (term38 _113204 B s f x) = (term38 _113204 B s f x).
Proof. exact (MK_COMB (@lem4963865 _113204) (@lem4963864 _113204 B s f x)). Qed.
Lemma lem4963867 {_113204 B : Type'} (s : type686 _113204) (f : type685 _113204 B) : (term39 _113204 B s f) = (term39 _113204 B s f).
Proof. exact (fun_ext (fun x : _113204 -> Prop => @lem4963866 _113204 B s f x)). Qed.
Lemma lem4963868 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4963869 {_113204 B : Type'} (s : type686 _113204) (f : type685 _113204 B) : (term40 _113204 B s f) = (term40 _113204 B s f).
Proof. exact (MK_COMB (@lem4963868 _113204) (@lem4963867 _113204 B s f)). Qed.
Lemma lem4963880 {_113204 B : Type'} (f : type685 _113204 B) (s : type686 _113204) (t : B -> Prop) : (term41 _113204 B f s t) = (term41 _113204 B f s t).
Proof. exact (eq_refl (term41 _113204 B f s t)). Qed.
Lemma lem4963881 {_113204 B : Type'} (t : B -> Prop) (s : type686 _113204) (f : type685 _113204 B) : (term42 _113204 B t s f) = (term42 _113204 B t s f).
Proof. exact (MK_COMB (@lem4963880 _113204 B f s t) (@lem4963869 _113204 B s f)). Qed.
Lemma lem4963882 {_113204 B : Type'} (t : B -> Prop) (s : type686 _113204) : (term43 _113204 B t s) = (term43 _113204 B t s).
Proof. exact (fun_ext (fun f : type685 _113204 B => @lem4963881 _113204 B t s f)). Qed.
Lemma lem4963883 {_113204 B : Type'} : (@all ((_113204 -> Prop) -> B)) = (@all ((_113204 -> Prop) -> B)).
Proof. exact (eq_refl (@all ((_113204 -> Prop) -> B))). Qed.
Lemma lem4963884 {_113204 B : Type'} (t : B -> Prop) (s : type686 _113204) : (term44 _113204 B t s) = (term44 _113204 B t s).
Proof. exact (MK_COMB (@lem4963883 _113204 B) (@lem4963882 _113204 B t s)). Qed.
Lemma lem4963885 {_113204 B : Type'} (s : type686 _113204) : (term45 _113204 B s) = (term45 _113204 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4963884 _113204 B t s)). Qed.
Lemma lem4963886 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4963887 {_113204 B : Type'} (s : type686 _113204) : (term46 _113204 B s) = (term46 _113204 B s).
Proof. exact (MK_COMB (@lem4963886 B) (@lem4963885 _113204 B s)). Qed.
Lemma lem4963888 {_113204 B : Type'} : (term47 _113204 B) = (term47 _113204 B).
Proof. exact (fun_ext (fun s : type686 _113204 => @lem4963887 _113204 B s)). Qed.
Lemma lem4963889 {_113204 : Type'} : (@all ((_113204 -> Prop) -> Prop)) = (@all ((_113204 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_113204 -> Prop) -> Prop))). Qed.
Lemma lem4963890 {_113204 B : Type'} : (term15 _113204 B) = (term15 _113204 B).
Proof. exact (MK_COMB (@lem4963889 _113204) (@lem4963888 _113204 B)). Qed.
Lemma lem4963891 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4963892 {_113204 B : Type'} : (term21 _113204 B) = (term21 _113204 B).
Proof. exact (MK_COMB (@lem4963891) (@lem4963890 _113204 B)). Qed.
Lemma lem4963905 {_113204 A : Type'} (s : A -> Prop) (f : type1470 _113204 A) (x : A) (y : A) : (term48 _113204 A s f x y) = (term48 _113204 A s f x y).
Proof. exact (eq_refl (term48 _113204 A s f x y)). Qed.
Lemma lem4963906 {_113204 A : Type'} (s : A -> Prop) (f : type1470 _113204 A) (x : A) : (term49 _113204 A s f x) = (term49 _113204 A s f x).
Proof. exact (fun_ext (fun y : A => @lem4963905 _113204 A s f x y)). Qed.
Lemma lem4963907 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4963908 {_113204 A : Type'} (s : A -> Prop) (f : type1470 _113204 A) (x : A) : (term50 _113204 A s f x) = (term50 _113204 A s f x).
Proof. exact (MK_COMB (@lem4963907 A) (@lem4963906 _113204 A s f x)). Qed.
Lemma lem4963909 {_113204 A : Type'} (s : A -> Prop) (f : type1470 _113204 A) : (term51 _113204 A s f) = (term51 _113204 A s f).
Proof. exact (fun_ext (fun x : A => @lem4963908 _113204 A s f x)). Qed.
Lemma lem4963910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4963911 {_113204 A : Type'} (s : A -> Prop) (f : type1470 _113204 A) : (term52 _113204 A s f) = (term52 _113204 A s f).
Proof. exact (MK_COMB (@lem4963910 A) (@lem4963909 _113204 A s f)). Qed.
Lemma lem4963922 {_113204 A : Type'} (f : type1470 _113204 A) (s : A -> Prop) (t : type686 _113204) : (term53 _113204 A f s t) = (term53 _113204 A f s t).
Proof. exact (eq_refl (term53 _113204 A f s t)). Qed.
Lemma lem4963923 {_113204 A : Type'} (t : type686 _113204) (s : A -> Prop) (f : type1470 _113204 A) : (term54 _113204 A t s f) = (term54 _113204 A t s f).
Proof. exact (MK_COMB (@lem4963922 _113204 A f s t) (@lem4963911 _113204 A s f)). Qed.
Lemma lem4963924 {_113204 A : Type'} (t : type686 _113204) (s : A -> Prop) : (term55 _113204 A t s) = (term55 _113204 A t s).
Proof. exact (fun_ext (fun f : type1470 _113204 A => @lem4963923 _113204 A t s f)). Qed.
Lemma lem4963925 {_113204 A : Type'} : (@all (A -> _113204 -> Prop)) = (@all (A -> _113204 -> Prop)).
Proof. exact (eq_refl (@all (A -> _113204 -> Prop))). Qed.
Lemma lem4963926 {_113204 A : Type'} (t : type686 _113204) (s : A -> Prop) : (term56 _113204 A t s) = (term56 _113204 A t s).
Proof. exact (MK_COMB (@lem4963925 _113204 A) (@lem4963924 _113204 A t s)). Qed.
Lemma lem4963927 {_113204 A : Type'} (s : A -> Prop) : (term57 _113204 A s) = (term57 _113204 A s).
Proof. exact (fun_ext (fun t : type686 _113204 => @lem4963926 _113204 A t s)). Qed.
Lemma lem4963928 {_113204 : Type'} : (@all ((_113204 -> Prop) -> Prop)) = (@all ((_113204 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_113204 -> Prop) -> Prop))). Qed.
Lemma lem4963929 {_113204 A : Type'} (s : A -> Prop) : (term58 _113204 A s) = (term58 _113204 A s).
Proof. exact (MK_COMB (@lem4963928 _113204) (@lem4963927 _113204 A s)). Qed.
Lemma lem4963930 {_113204 A : Type'} : (term59 _113204 A) = (term59 _113204 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4963929 _113204 A s)). Qed.
Lemma lem4963931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4963932 {_113204 A : Type'} : (term14 _113204 A) = (term14 _113204 A).
Proof. exact (MK_COMB (@lem4963931 A) (@lem4963930 _113204 A)). Qed.
Lemma lem4963933 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4963934 {_113204 A : Type'} : (term22 _113204 A) = (term22 _113204 A).
Proof. exact (MK_COMB (@lem4963933) (@lem4963932 _113204 A)). Qed.
Lemma lem4963935 {_113204 A B : Type'} : (term24 _113204 A B) = (term24 _113204 A B).
Proof. exact (MK_COMB (@lem4963934 _113204 A) (@lem4963892 _113204 B)). Qed.
Lemma lem4963948 {_113204 A : Type'} (s : A -> Prop) (f : A -> _113204) (x : A) (y : A) : (term60 _113204 A s f x y) = (term60 _113204 A s f x y).
Proof. exact (eq_refl (term60 _113204 A s f x y)). Qed.
Lemma lem4963949 {_113204 A : Type'} (s : A -> Prop) (f : A -> _113204) (x : A) : (term61 _113204 A s f x) = (term61 _113204 A s f x).
Proof. exact (fun_ext (fun y : A => @lem4963948 _113204 A s f x y)). Qed.
Lemma lem4963950 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4963951 {_113204 A : Type'} (s : A -> Prop) (f : A -> _113204) (x : A) : (term62 _113204 A s f x) = (term62 _113204 A s f x).
Proof. exact (MK_COMB (@lem4963950 A) (@lem4963949 _113204 A s f x)). Qed.
Lemma lem4963952 {_113204 A : Type'} (s : A -> Prop) (f : A -> _113204) : (term63 _113204 A s f) = (term63 _113204 A s f).
Proof. exact (fun_ext (fun x : A => @lem4963951 _113204 A s f x)). Qed.
Lemma lem4963953 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4963954 {_113204 A : Type'} (s : A -> Prop) (f : A -> _113204) : (term64 _113204 A s f) = (term64 _113204 A s f).
Proof. exact (MK_COMB (@lem4963953 A) (@lem4963952 _113204 A s f)). Qed.
Lemma lem4963965 {_113204 A : Type'} (f : A -> _113204) (s : A -> Prop) (t : _113204 -> Prop) : (term65 _113204 A f s t) = (term65 _113204 A f s t).
Proof. exact (eq_refl (term65 _113204 A f s t)). Qed.
Lemma lem4963966 {_113204 A : Type'} (t : _113204 -> Prop) (s : A -> Prop) (f : A -> _113204) : (term66 _113204 A t s f) = (term66 _113204 A t s f).
Proof. exact (MK_COMB (@lem4963965 _113204 A f s t) (@lem4963954 _113204 A s f)). Qed.
Lemma lem4963967 {_113204 A : Type'} (t : _113204 -> Prop) (s : A -> Prop) : (term67 _113204 A t s) = (term67 _113204 A t s).
Proof. exact (fun_ext (fun f : A -> _113204 => @lem4963966 _113204 A t s f)). Qed.
Lemma lem4963968 {_113204 A : Type'} : (@all (A -> _113204)) = (@all (A -> _113204)).
Proof. exact (eq_refl (@all (A -> _113204))). Qed.
Lemma lem4963969 {_113204 A : Type'} (t : _113204 -> Prop) (s : A -> Prop) : (term68 _113204 A t s) = (term68 _113204 A t s).
Proof. exact (MK_COMB (@lem4963968 _113204 A) (@lem4963967 _113204 A t s)). Qed.
Lemma lem4963970 {_113204 A : Type'} (s : A -> Prop) : (term69 _113204 A s) = (term69 _113204 A s).
Proof. exact (fun_ext (fun t : _113204 -> Prop => @lem4963969 _113204 A t s)). Qed.
Lemma lem4963971 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4963972 {_113204 A : Type'} (s : A -> Prop) : (term70 _113204 A s) = (term70 _113204 A s).
Proof. exact (MK_COMB (@lem4963971 _113204) (@lem4963970 _113204 A s)). Qed.
Lemma lem4963973 {_113204 A : Type'} : (term71 _113204 A) = (term71 _113204 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4963972 _113204 A s)). Qed.
Lemma lem4963974 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4963975 {_113204 A : Type'} : (term12 _113204 A) = (term12 _113204 A).
Proof. exact (MK_COMB (@lem4963974 A) (@lem4963973 _113204 A)). Qed.
Lemma lem4963976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4963977 {_113204 A : Type'} : (term25 _113204 A) = (term25 _113204 A).
Proof. exact (MK_COMB (@lem4963976) (@lem4963975 _113204 A)). Qed.
Lemma lem4963978 {_113204 A B : Type'} : (term27 _113204 A B) = (term27 _113204 A B).
Proof. exact (MK_COMB (@lem4963977 _113204 A) (@lem4963935 _113204 A B)). Qed.
Lemma lem4963991 {_113204 B : Type'} (s : _113204 -> Prop) (f : _113204 -> B) (x : _113204) (y : _113204) : (term72 _113204 B s f x y) = (term72 _113204 B s f x y).
Proof. exact (eq_refl (term72 _113204 B s f x y)). Qed.
Lemma lem4963992 {_113204 B : Type'} (s : _113204 -> Prop) (f : _113204 -> B) (x : _113204) : (term73 _113204 B s f x) = (term73 _113204 B s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4963991 _113204 B s f x y)). Qed.
Lemma lem4963993 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4963994 {_113204 B : Type'} (s : _113204 -> Prop) (f : _113204 -> B) (x : _113204) : (term74 _113204 B s f x) = (term74 _113204 B s f x).
Proof. exact (MK_COMB (@lem4963993 _113204) (@lem4963992 _113204 B s f x)). Qed.
Lemma lem4963995 {_113204 B : Type'} (s : _113204 -> Prop) (f : _113204 -> B) : (term75 _113204 B s f) = (term75 _113204 B s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4963994 _113204 B s f x)). Qed.
Lemma lem4963996 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4963997 {_113204 B : Type'} (s : _113204 -> Prop) (f : _113204 -> B) : (term76 _113204 B s f) = (term76 _113204 B s f).
Proof. exact (MK_COMB (@lem4963996 _113204) (@lem4963995 _113204 B s f)). Qed.
Lemma lem4964008 {_113204 B : Type'} (f : _113204 -> B) (s : _113204 -> Prop) (t : B -> Prop) : (term77 _113204 B f s t) = (term77 _113204 B f s t).
Proof. exact (eq_refl (term77 _113204 B f s t)). Qed.
Lemma lem4964009 {_113204 B : Type'} (t : B -> Prop) (s : _113204 -> Prop) (f : _113204 -> B) : (term78 _113204 B t s f) = (term78 _113204 B t s f).
Proof. exact (MK_COMB (@lem4964008 _113204 B f s t) (@lem4963997 _113204 B s f)). Qed.
Lemma lem4964010 {_113204 B : Type'} (t : B -> Prop) (s : _113204 -> Prop) : (term79 _113204 B t s) = (term79 _113204 B t s).
Proof. exact (fun_ext (fun f : _113204 -> B => @lem4964009 _113204 B t s f)). Qed.
Lemma lem4964011 {_113204 B : Type'} : (@all (_113204 -> B)) = (@all (_113204 -> B)).
Proof. exact (eq_refl (@all (_113204 -> B))). Qed.
Lemma lem4964012 {_113204 B : Type'} (t : B -> Prop) (s : _113204 -> Prop) : (term80 _113204 B t s) = (term80 _113204 B t s).
Proof. exact (MK_COMB (@lem4964011 _113204 B) (@lem4964010 _113204 B t s)). Qed.
Lemma lem4964013 {_113204 B : Type'} (s : _113204 -> Prop) : (term81 _113204 B s) = (term81 _113204 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4964012 _113204 B t s)). Qed.
Lemma lem4964014 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4964015 {_113204 B : Type'} (s : _113204 -> Prop) : (term82 _113204 B s) = (term82 _113204 B s).
Proof. exact (MK_COMB (@lem4964014 B) (@lem4964013 _113204 B s)). Qed.
Lemma lem4964016 {_113204 B : Type'} : (term83 _113204 B) = (term83 _113204 B).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4964015 _113204 B s)). Qed.
Lemma lem4964017 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4964018 {_113204 B : Type'} : (term11 _113204 B) = (term11 _113204 B).
Proof. exact (MK_COMB (@lem4964017 _113204) (@lem4964016 _113204 B)). Qed.
Lemma lem4964019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4964020 {_113204 B : Type'} : (term28 _113204 B) = (term28 _113204 B).
Proof. exact (MK_COMB (@lem4964019) (@lem4964018 _113204 B)). Qed.
Lemma lem4964021 {_113204 A B : Type'} : (term30 _113204 A B) = (term30 _113204 A B).
Proof. exact (MK_COMB (@lem4964020 _113204 B) (@lem4963978 _113204 A B)). Qed.
Lemma lem4964034 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term84 _113204 s f x y) = (term84 _113204 s f x y).
Proof. exact (eq_refl (term84 _113204 s f x y)). Qed.
Lemma lem4964035 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term85 _113204 s f x) = (term85 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4964034 _113204 s f x y)). Qed.
Lemma lem4964036 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4964037 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term86 _113204 s f x) = (term86 _113204 s f x).
Proof. exact (MK_COMB (@lem4964036 _113204) (@lem4964035 _113204 s f x)). Qed.
Lemma lem4964038 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term87 _113204 s f) = (term87 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4964037 _113204 s f x)). Qed.
Lemma lem4964039 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4964040 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term88 _113204 s f) = (term88 _113204 s f).
Proof. exact (MK_COMB (@lem4964039 _113204) (@lem4964038 _113204 s f)). Qed.
Lemma lem4964051 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term89 _113204 f s t) = (term89 _113204 f s t).
Proof. exact (eq_refl (term89 _113204 f s t)). Qed.
Lemma lem4964052 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term90 _113204 t s f) = (term90 _113204 t s f).
Proof. exact (MK_COMB (@lem4964051 _113204 f s t) (@lem4964040 _113204 s f)). Qed.
Lemma lem4964053 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term91 _113204 t s) = (term91 _113204 t s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4964052 _113204 t s f)). Qed.
Lemma lem4964054 {_113204 : Type'} : (@all (_113204 -> _113204)) = (@all (_113204 -> _113204)).
Proof. exact (eq_refl (@all (_113204 -> _113204))). Qed.
Lemma lem4964055 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term92 _113204 t s) = (term92 _113204 t s).
Proof. exact (MK_COMB (@lem4964054 _113204) (@lem4964053 _113204 t s)). Qed.
Lemma lem4964056 {_113204 : Type'} (s : _113204 -> Prop) : (term93 _113204 s) = (term93 _113204 s).
Proof. exact (fun_ext (fun t : _113204 -> Prop => @lem4964055 _113204 t s)). Qed.
Lemma lem4964057 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4964058 {_113204 : Type'} (s : _113204 -> Prop) : (term94 _113204 s) = (term94 _113204 s).
Proof. exact (MK_COMB (@lem4964057 _113204) (@lem4964056 _113204 s)). Qed.
Lemma lem4964059 {_113204 : Type'} : (term95 _113204) = (term95 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4964058 _113204 s)). Qed.
Lemma lem4964060 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4964061 {_113204 : Type'} : (term13 _113204) = (term13 _113204).
Proof. exact (MK_COMB (@lem4964060 _113204) (@lem4964059 _113204)). Qed.
Lemma lem4964062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4964063 {_113204 : Type'} : (term31 _113204) = (term31 _113204).
Proof. exact (MK_COMB (@lem4964062) (@lem4964061 _113204)). Qed.
Lemma lem4964064 {_113204 A B : Type'} : (term33 _113204 A B) = (term33 _113204 A B).
Proof. exact (MK_COMB (@lem4964063 _113204) (@lem4964021 _113204 A B)). Qed.
Lemma lem4964077 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term84 _113204 s f x y) = (term84 _113204 s f x y).
Proof. exact (eq_refl (term84 _113204 s f x y)). Qed.
Lemma lem4964078 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term85 _113204 s f x) = (term85 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4964077 _113204 s f x y)). Qed.
Lemma lem4964079 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4964080 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term86 _113204 s f x) = (term86 _113204 s f x).
Proof. exact (MK_COMB (@lem4964079 _113204) (@lem4964078 _113204 s f x)). Qed.
Lemma lem4964081 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term87 _113204 s f) = (term87 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4964080 _113204 s f x)). Qed.
Lemma lem4964082 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4964083 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term88 _113204 s f) = (term88 _113204 s f).
Proof. exact (MK_COMB (@lem4964082 _113204) (@lem4964081 _113204 s f)). Qed.
Lemma lem4964090 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term96 _113204 f s) = (term96 _113204 f s).
Proof. exact (eq_refl (term96 _113204 f s)). Qed.
Lemma lem4964091 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term97 _113204 s f) = (term97 _113204 s f).
Proof. exact (MK_COMB (@lem4964090 _113204 f s) (@lem4964083 _113204 s f)). Qed.
Lemma lem4964092 {_113204 : Type'} (s : _113204 -> Prop) : (term98 _113204 s) = (term98 _113204 s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4964091 _113204 s f)). Qed.
Lemma lem4964093 {_113204 : Type'} : (@all (_113204 -> _113204)) = (@all (_113204 -> _113204)).
Proof. exact (eq_refl (@all (_113204 -> _113204))). Qed.
Lemma lem4964094 {_113204 : Type'} (s : _113204 -> Prop) : (term99 _113204 s) = (term99 _113204 s).
Proof. exact (MK_COMB (@lem4964093 _113204) (@lem4964092 _113204 s)). Qed.
Lemma lem4964095 {_113204 : Type'} : (term100 _113204) = (term100 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4964094 _113204 s)). Qed.
Lemma lem4964096 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4964097 {_113204 : Type'} : (term8 _113204) = (term8 _113204).
Proof. exact (MK_COMB (@lem4964096 _113204) (@lem4964095 _113204)). Qed.
Lemma lem4964098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4964099 {_113204 : Type'} : (term10 _113204) = (term10 _113204).
Proof. exact (MK_COMB (@lem4964098) (@lem4964097 _113204)). Qed.
Lemma lem4964100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4964101 {_113204 : Type'} : (term34 _113204) = (term34 _113204).
Proof. exact (MK_COMB (@lem4964100) (@lem4964099 _113204)). Qed.
Lemma lem4964102 {_113204 A B : Type'} : (term35 _113204 A B) = (term35 _113204 A B).
Proof. exact (MK_COMB (@lem4964101 _113204) (@lem4964064 _113204 A B)). Qed.
Lemma lem4964359 {_113204 A B : Type'} : (term16 _113204 A B) = (term35 _113204 A B).
Proof. exact (TRANS (@lem4963850 _113204 A B) (@lem4964102 _113204 A B)). Qed.
Lemma lem4964360 {_113204 A B : Type'} : (term35 _113204 A B) = (term16 _113204 A B).
Proof. exact (SYM (@lem4964359 _113204 A B)). Qed.
Lemma lem4964361 {_113204 : Type'} (h1 : term10 _113204) : term10 _113204.
Proof. exact (h1). Qed.
Lemma lem4964362 {_113204 : Type'} (h1 : term13 _113204) : term13 _113204.
Proof. exact (h1). Qed.
Lemma lem4964386 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term101 _113204 s f x y) = (term102 _113204 s f x y).
Proof. exact (@lem17362 (term103 _113204 s x f y) (x = y)). Qed.
Lemma lem4964387 {_113204 : Type'} (P : _113204 -> Prop) : (term104 _113204 P) = (term105 _113204 P).
Proof. exact (@lem18392 _113204 P). Qed.
Lemma lem4964388 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term106 _113204 s f x) = (term107 _113204 s f x).
Proof. exact (@lem4964387 _113204 (term85 _113204 s f x)). Qed.
Lemma lem4964389 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term108 _113204 s f x y) = (term84 _113204 s f x y).
Proof. exact (eq_refl (term108 _113204 s f x y)). Qed.
Lemma lem4964390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4964391 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term109 _113204 s f x y) = (term101 _113204 s f x y).
Proof. exact (MK_COMB (@lem4964390) (@lem4964389 _113204 s f x y)). Qed.
Lemma lem4964392 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term109 _113204 s f x y) = (term102 _113204 s f x y).
Proof. exact (TRANS (@lem4964391 _113204 s f x y) (@lem4964386 _113204 s f x y)). Qed.
Lemma lem4964393 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term110 _113204 s f x) = (term111 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4964392 _113204 s f x y)). Qed.
Lemma lem4964394 {_113204 : Type'} : (@ex _113204) = (@ex _113204).
Proof. exact (eq_refl (@ex _113204)). Qed.
Lemma lem4964395 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term107 _113204 s f x) = (term112 _113204 s f x).
Proof. exact (MK_COMB (@lem4964394 _113204) (@lem4964393 _113204 s f x)). Qed.
Lemma lem4964396 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term106 _113204 s f x) = (term112 _113204 s f x).
Proof. exact (TRANS (@lem4964388 _113204 s f x) (@lem4964395 _113204 s f x)). Qed.
Lemma lem4964397 {_113204 : Type'} (P : _113204 -> Prop) : (term104 _113204 P) = (term105 _113204 P).
Proof. exact (@lem18392 _113204 P). Qed.
Lemma lem4964398 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term113 _113204 s f) = (term114 _113204 s f).
Proof. exact (@lem4964397 _113204 (term87 _113204 s f)). Qed.
Lemma lem4964399 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term115 _113204 s f x) = (term86 _113204 s f x).
Proof. exact (eq_refl (term115 _113204 s f x)). Qed.
Lemma lem4964400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4964401 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term116 _113204 s f x) = (term106 _113204 s f x).
Proof. exact (MK_COMB (@lem4964400) (@lem4964399 _113204 s f x)). Qed.
Lemma lem4964402 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term116 _113204 s f x) = (term112 _113204 s f x).
Proof. exact (TRANS (@lem4964401 _113204 s f x) (@lem4964396 _113204 s f x)). Qed.
Lemma lem4964403 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term117 _113204 s f) = (term118 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4964402 _113204 s f x)). Qed.
Lemma lem4964404 {_113204 : Type'} : (@ex _113204) = (@ex _113204).
Proof. exact (eq_refl (@ex _113204)). Qed.
Lemma lem4964405 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term114 _113204 s f) = (term119 _113204 s f).
Proof. exact (MK_COMB (@lem4964404 _113204) (@lem4964403 _113204 s f)). Qed.
Lemma lem4964406 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term113 _113204 s f) = (term119 _113204 s f).
Proof. exact (TRANS (@lem4964398 _113204 s f) (@lem4964405 _113204 s f)). Qed.
Lemma lem4964408 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term120 _113204 f s) = (term120 _113204 f s).
Proof. exact (eq_refl (term120 _113204 f s)). Qed.
Lemma lem4964409 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term121 _113204 s f) = (term122 _113204 s f).
Proof. exact (MK_COMB (@lem4964408 _113204 f s) (@lem4964406 _113204 s f)). Qed.
Lemma lem4964410 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term123 _113204 s f) = (term121 _113204 s f).
Proof. exact (@lem17362 (term124 _113204 f s) (term88 _113204 s f)). Qed.
Lemma lem4964411 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term123 _113204 s f) = (term122 _113204 s f).
Proof. exact (TRANS (@lem4964410 _113204 s f) (@lem4964409 _113204 s f)). Qed.
Lemma lem4964412 {_113204 : Type'} (P : type488 _113204) : (term125 _113204 P) = (term126 _113204 P).
Proof. exact (@lem18392 (_113204 -> _113204) P). Qed.
Lemma lem4964413 {_113204 : Type'} (s : _113204 -> Prop) : (term127 _113204 s) = (term128 _113204 s).
Proof. exact (@lem4964412 _113204 (term98 _113204 s)). Qed.
Lemma lem4964414 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term129 _113204 s f) = (term97 _113204 s f).
Proof. exact (eq_refl (term129 _113204 s f)). Qed.
Lemma lem4964415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4964416 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term130 _113204 s f) = (term123 _113204 s f).
Proof. exact (MK_COMB (@lem4964415) (@lem4964414 _113204 s f)). Qed.
Lemma lem4964417 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term130 _113204 s f) = (term122 _113204 s f).
Proof. exact (TRANS (@lem4964416 _113204 s f) (@lem4964411 _113204 s f)). Qed.
Lemma lem4964418 {_113204 : Type'} (s : _113204 -> Prop) : (term131 _113204 s) = (term132 _113204 s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4964417 _113204 s f)). Qed.
Lemma lem4964419 {_113204 : Type'} : (@ex (_113204 -> _113204)) = (@ex (_113204 -> _113204)).
Proof. exact (eq_refl (@ex (_113204 -> _113204))). Qed.
Lemma lem4964420 {_113204 : Type'} (s : _113204 -> Prop) : (term128 _113204 s) = (term133 _113204 s).
Proof. exact (MK_COMB (@lem4964419 _113204) (@lem4964418 _113204 s)). Qed.
Lemma lem4964421 {_113204 : Type'} (s : _113204 -> Prop) : (term127 _113204 s) = (term133 _113204 s).
Proof. exact (TRANS (@lem4964413 _113204 s) (@lem4964420 _113204 s)). Qed.
Lemma lem4964422 {_113204 : Type'} (P : type686 _113204) : (term134 _113204 P) = (term135 _113204 P).
Proof. exact (@lem18392 (_113204 -> Prop) P). Qed.
Lemma lem4964423 {_113204 : Type'} : (term10 _113204) = (term136 _113204).
Proof. exact (@lem4964422 _113204 (term100 _113204)). Qed.
Lemma lem4964424 {_113204 : Type'} (s : _113204 -> Prop) : (term137 _113204 s) = (term99 _113204 s).
Proof. exact (eq_refl (term137 _113204 s)). Qed.
Lemma lem4964425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4964426 {_113204 : Type'} (s : _113204 -> Prop) : (term138 _113204 s) = (term127 _113204 s).
Proof. exact (MK_COMB (@lem4964425) (@lem4964424 _113204 s)). Qed.
Lemma lem4964427 {_113204 : Type'} (s : _113204 -> Prop) : (term138 _113204 s) = (term133 _113204 s).
Proof. exact (TRANS (@lem4964426 _113204 s) (@lem4964421 _113204 s)). Qed.
Lemma lem4964428 {_113204 : Type'} : (term139 _113204) = (term140 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4964427 _113204 s)). Qed.
Lemma lem4964429 {_113204 : Type'} : (@ex (_113204 -> Prop)) = (@ex (_113204 -> Prop)).
Proof. exact (eq_refl (@ex (_113204 -> Prop))). Qed.
Lemma lem4964430 {_113204 : Type'} : (term136 _113204) = (term141 _113204).
Proof. exact (MK_COMB (@lem4964429 _113204) (@lem4964428 _113204)). Qed.
Lemma lem4964431 {_113204 : Type'} : (term10 _113204) = (term141 _113204).
Proof. exact (TRANS (@lem4964423 _113204) (@lem4964430 _113204)). Qed.
Lemma lem4964538 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4964539 {_113204 : Type'} (P : Prop) (Q : _113204 -> Prop) : (term142 _113204 P Q) = (term143 _113204 P Q).
Proof. exact (@lem4964538 _113204 P Q). Qed.
Lemma lem4964540 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term144 _113204 s f) = (term145 _113204 s f).
Proof. exact (@lem4964539 _113204 (term124 _113204 f s) (term118 _113204 s f)). Qed.
Lemma lem4964541 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term146 _113204 s f x) = (term112 _113204 s f x).
Proof. exact (eq_refl (term146 _113204 s f x)). Qed.
Lemma lem4964542 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term147 _113204 s f) = (term118 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4964541 _113204 s f x)). Qed.
Lemma lem4964543 {_113204 : Type'} : (@ex _113204) = (@ex _113204).
Proof. exact (eq_refl (@ex _113204)). Qed.
Lemma lem4964544 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term148 _113204 s f) = (term119 _113204 s f).
Proof. exact (MK_COMB (@lem4964543 _113204) (@lem4964542 _113204 s f)). Qed.
Lemma lem4964545 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term120 _113204 f s) = (term120 _113204 f s).
Proof. exact (eq_refl (term120 _113204 f s)). Qed.
Lemma lem4964546 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term144 _113204 s f) = (term122 _113204 s f).
Proof. exact (MK_COMB (@lem4964545 _113204 f s) (@lem4964544 _113204 s f)). Qed.
Lemma lem4964547 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4964548 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term149 _113204 s f) = (term150 _113204 s f).
Proof. exact (MK_COMB (@lem4964547) (@lem4964546 _113204 s f)). Qed.
Lemma lem4964549 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term146 _113204 s f x) = (term112 _113204 s f x).
Proof. exact (eq_refl (term146 _113204 s f x)). Qed.
Lemma lem4964550 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term120 _113204 f s) = (term120 _113204 f s).
Proof. exact (eq_refl (term120 _113204 f s)). Qed.
Lemma lem4964551 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term151 _113204 s f x) = (term152 _113204 s f x).
Proof. exact (MK_COMB (@lem4964550 _113204 f s) (@lem4964549 _113204 s f x)). Qed.
Lemma lem4964552 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term153 _113204 s f) = (term154 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4964551 _113204 s f x)). Qed.
Lemma lem4964553 {_113204 : Type'} : (@ex _113204) = (@ex _113204).
Proof. exact (eq_refl (@ex _113204)). Qed.
Lemma lem4964554 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term145 _113204 s f) = (term155 _113204 s f).
Proof. exact (MK_COMB (@lem4964553 _113204) (@lem4964552 _113204 s f)). Qed.
Lemma lem4964555 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : ((term144 _113204 s f) = (term145 _113204 s f)) = ((term122 _113204 s f) = (term155 _113204 s f)).
Proof. exact (MK_COMB (@lem4964548 _113204 s f) (@lem4964554 _113204 s f)). Qed.
Lemma lem4964556 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term122 _113204 s f) = (term155 _113204 s f).
Proof. exact (EQ_MP (@lem4964555 _113204 s f) (@lem4964540 _113204 s f)). Qed.
Lemma lem4964558 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4964559 {_113204 : Type'} (P : Prop) (Q : _113204 -> Prop) : (term142 _113204 P Q) = (term143 _113204 P Q).
Proof. exact (@lem4964558 _113204 P Q). Qed.
Lemma lem4964560 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term156 _113204 s f x) = (term157 _113204 s f x).
Proof. exact (@lem4964559 _113204 (term124 _113204 f s) (term111 _113204 s f x)). Qed.
Lemma lem4964561 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term158 _113204 s f x y) = (term102 _113204 s f x y).
Proof. exact (eq_refl (term158 _113204 s f x y)). Qed.
Lemma lem4964562 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term159 _113204 s f x) = (term111 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4964561 _113204 s f x y)). Qed.
Lemma lem4964563 {_113204 : Type'} : (@ex _113204) = (@ex _113204).
Proof. exact (eq_refl (@ex _113204)). Qed.
Lemma lem4964564 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term160 _113204 s f x) = (term112 _113204 s f x).
Proof. exact (MK_COMB (@lem4964563 _113204) (@lem4964562 _113204 s f x)). Qed.
Lemma lem4964565 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term120 _113204 f s) = (term120 _113204 f s).
Proof. exact (eq_refl (term120 _113204 f s)). Qed.
Lemma lem4964566 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term156 _113204 s f x) = (term152 _113204 s f x).
Proof. exact (MK_COMB (@lem4964565 _113204 f s) (@lem4964564 _113204 s f x)). Qed.
Lemma lem4964567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4964568 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term161 _113204 s f x) = (term162 _113204 s f x).
Proof. exact (MK_COMB (@lem4964567) (@lem4964566 _113204 s f x)). Qed.
Lemma lem4964569 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term158 _113204 s f x y) = (term102 _113204 s f x y).
Proof. exact (eq_refl (term158 _113204 s f x y)). Qed.
Lemma lem4964570 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term120 _113204 f s) = (term120 _113204 f s).
Proof. exact (eq_refl (term120 _113204 f s)). Qed.
Lemma lem4964571 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term163 _113204 s f x y) = (term164 _113204 s f x y).
Proof. exact (MK_COMB (@lem4964570 _113204 f s) (@lem4964569 _113204 s f x y)). Qed.
Lemma lem4964572 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term165 _113204 s f x) = (term166 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4964571 _113204 s f x y)). Qed.
Lemma lem4964573 {_113204 : Type'} : (@ex _113204) = (@ex _113204).
Proof. exact (eq_refl (@ex _113204)). Qed.
Lemma lem4964574 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term157 _113204 s f x) = (term167 _113204 s f x).
Proof. exact (MK_COMB (@lem4964573 _113204) (@lem4964572 _113204 s f x)). Qed.
Lemma lem4964575 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : ((term156 _113204 s f x) = (term157 _113204 s f x)) = ((term152 _113204 s f x) = (term167 _113204 s f x)).
Proof. exact (MK_COMB (@lem4964568 _113204 s f x) (@lem4964574 _113204 s f x)). Qed.
Lemma lem4964576 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term152 _113204 s f x) = (term167 _113204 s f x).
Proof. exact (EQ_MP (@lem4964575 _113204 s f x) (@lem4964560 _113204 s f x)). Qed.
Lemma lem4964577 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term154 _113204 s f) = (term168 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4964576 _113204 s f x)). Qed.
Lemma lem4964578 {_113204 : Type'} : (@ex _113204) = (@ex _113204).
Proof. exact (eq_refl (@ex _113204)). Qed.
Lemma lem4964579 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term155 _113204 s f) = (term169 _113204 s f).
Proof. exact (MK_COMB (@lem4964578 _113204) (@lem4964577 _113204 s f)). Qed.
Lemma lem4964580 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term122 _113204 s f) = (term169 _113204 s f).
Proof. exact (TRANS (@lem4964556 _113204 s f) (@lem4964579 _113204 s f)). Qed.
Lemma lem4964581 {_113204 : Type'} (s : _113204 -> Prop) : (term132 _113204 s) = (term170 _113204 s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4964580 _113204 s f)). Qed.
Lemma lem4964582 {_113204 : Type'} : (@ex (_113204 -> _113204)) = (@ex (_113204 -> _113204)).
Proof. exact (eq_refl (@ex (_113204 -> _113204))). Qed.
Lemma lem4964583 {_113204 : Type'} (s : _113204 -> Prop) : (term133 _113204 s) = (term171 _113204 s).
Proof. exact (MK_COMB (@lem4964582 _113204) (@lem4964581 _113204 s)). Qed.
Lemma lem4964584 {_113204 : Type'} : (term140 _113204) = (term172 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4964583 _113204 s)). Qed.
Lemma lem4964585 {_113204 : Type'} : (@ex (_113204 -> Prop)) = (@ex (_113204 -> Prop)).
Proof. exact (eq_refl (@ex (_113204 -> Prop))). Qed.
Lemma lem4964587 {_113204 : Type'} : (term141 _113204) = (term173 _113204).
Proof. exact (MK_COMB (@lem4964585 _113204) (@lem4964584 _113204)). Qed.
Lemma lem4964588 {_113204 : Type'} : (term10 _113204) = (term173 _113204).
Proof. exact (TRANS (@lem4964431 _113204) (@lem4964587 _113204)). Qed.
Lemma lem4964589 {_113204 : Type'} (h1 : term10 _113204) : term173 _113204.
Proof. exact (EQ_MP (@lem4964588 _113204) (@lem4964361 _113204 h1)). Qed.
Lemma lem4964597 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term174 _113204 f s t) = (term175 _113204 f s t).
Proof. exact (@lem17045 ((@CARD _113204 s) = (@CARD _113204 t)) ((@IMAGE _113204 _113204 f s) = t)). Qed.
Lemma lem4964599 {_113204 : Type'} (s : _113204 -> Prop) : (term176 _113204 s) = (term176 _113204 s).
Proof. exact (eq_refl (term176 _113204 s)). Qed.
Lemma lem4964600 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term177 _113204 f s t) = (term178 _113204 f s t).
Proof. exact (MK_COMB (@lem4964599 _113204 s) (@lem4964597 _113204 f s t)). Qed.
Lemma lem4964601 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term179 _113204 f s t) = (term177 _113204 f s t).
Proof. exact (@lem17045 (@FINITE _113204 s) (term180 _113204 f s t)). Qed.
Lemma lem4964602 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term179 _113204 f s t) = (term178 _113204 f s t).
Proof. exact (TRANS (@lem4964601 _113204 f s t) (@lem4964600 _113204 f s t)). Qed.
Lemma lem4964610 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term181 _113204 s x f y) = (term182 _113204 s x f y).
Proof. exact (@lem17045 (@IN _113204 y s) ((f x) = (f y))). Qed.
Lemma lem4964612 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (term183 _113204 x s) = (term183 _113204 x s).
Proof. exact (eq_refl (term183 _113204 x s)). Qed.
Lemma lem4964613 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term184 _113204 s x f y) = (term185 _113204 s x f y).
Proof. exact (MK_COMB (@lem4964612 _113204 x s) (@lem4964610 _113204 s x f y)). Qed.
Lemma lem4964614 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term186 _113204 s x f y) = (term184 _113204 s x f y).
Proof. exact (@lem17045 (@IN _113204 x s) (term187 _113204 s x f y)). Qed.
Lemma lem4964615 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term186 _113204 s x f y) = (term185 _113204 s x f y).
Proof. exact (TRANS (@lem4964614 _113204 s x f y) (@lem4964613 _113204 s x f y)). Qed.
Lemma lem4964616 {_113204 : Type'} (x : _113204) (y : _113204) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4964617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4964618 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term188 _113204 s x f y) = (term189 _113204 s x f y).
Proof. exact (MK_COMB (@lem4964617) (@lem4964615 _113204 s x f y)). Qed.
Lemma lem4964619 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term190 _113204 s f x y) = (term191 _113204 s f x y).
Proof. exact (MK_COMB (@lem4964618 _113204 s x f y) (@lem4964616 _113204 x y)). Qed.
Lemma lem4964620 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term84 _113204 s f x y) = (term190 _113204 s f x y).
Proof. exact (@lem17265 (term103 _113204 s x f y) (x = y)). Qed.
Lemma lem4964621 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term84 _113204 s f x y) = (term191 _113204 s f x y).
Proof. exact (TRANS (@lem4964620 _113204 s f x y) (@lem4964619 _113204 s f x y)). Qed.
Lemma lem4964622 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term85 _113204 s f x) = (term192 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4964621 _113204 s f x y)). Qed.
Lemma lem4964623 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4964624 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term86 _113204 s f x) = (term193 _113204 s f x).
Proof. exact (MK_COMB (@lem4964623 _113204) (@lem4964622 _113204 s f x)). Qed.
Lemma lem4964625 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term87 _113204 s f) = (term194 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4964624 _113204 s f x)). Qed.
Lemma lem4964626 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4964627 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term88 _113204 s f) = (term195 _113204 s f).
Proof. exact (MK_COMB (@lem4964626 _113204) (@lem4964625 _113204 s f)). Qed.
Lemma lem4964628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4964629 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term196 _113204 f s t) = (term197 _113204 f s t).
Proof. exact (MK_COMB (@lem4964628) (@lem4964602 _113204 f s t)). Qed.
Lemma lem4964630 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term198 _113204 t s f) = (term199 _113204 t s f).
Proof. exact (MK_COMB (@lem4964629 _113204 f s t) (@lem4964627 _113204 s f)). Qed.
Lemma lem4964631 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term90 _113204 t s f) = (term198 _113204 t s f).
Proof. exact (@lem17265 (term200 _113204 f s t) (term88 _113204 s f)). Qed.
Lemma lem4964632 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term90 _113204 t s f) = (term199 _113204 t s f).
Proof. exact (TRANS (@lem4964631 _113204 t s f) (@lem4964630 _113204 t s f)). Qed.
Lemma lem4964633 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term91 _113204 t s) = (term201 _113204 t s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4964632 _113204 t s f)). Qed.
Lemma lem4964634 {_113204 : Type'} : (@all (_113204 -> _113204)) = (@all (_113204 -> _113204)).
Proof. exact (eq_refl (@all (_113204 -> _113204))). Qed.
Lemma lem4964635 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term92 _113204 t s) = (term202 _113204 t s).
Proof. exact (MK_COMB (@lem4964634 _113204) (@lem4964633 _113204 t s)). Qed.
Lemma lem4964636 {_113204 : Type'} (s : _113204 -> Prop) : (term93 _113204 s) = (term203 _113204 s).
Proof. exact (fun_ext (fun t : _113204 -> Prop => @lem4964635 _113204 t s)). Qed.
Lemma lem4964637 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4964638 {_113204 : Type'} (s : _113204 -> Prop) : (term94 _113204 s) = (term204 _113204 s).
Proof. exact (MK_COMB (@lem4964637 _113204) (@lem4964636 _113204 s)). Qed.
Lemma lem4964639 {_113204 : Type'} : (term95 _113204) = (term205 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4964638 _113204 s)). Qed.
Lemma lem4964640 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4964753 {_113204 : Type'} : (term13 _113204) = (term206 _113204).
Proof. exact (MK_COMB (@lem4964640 _113204) (@lem4964639 _113204)). Qed.
Lemma lem4964754 {_113204 : Type'} (h1 : term13 _113204) : term206 _113204.
Proof. exact (EQ_MP (@lem4964753 _113204) (@lem4964362 _113204 h1)). Qed.
Lemma lem4965415 {_113204 : Type'} (s : _113204 -> Prop) (h1 : term171 _113204 s) : term171 _113204 s.
Proof. exact (h1). Qed.
Lemma lem4965416 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (h1 : term169 _113204 s f) : term169 _113204 s f.
Proof. exact (h1). Qed.
Lemma lem4965417 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (h1 : term167 _113204 s f x) : term167 _113204 s f x.
Proof. exact (h1). Qed.
Lemma lem4965418 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term164 _113204 s f x y.
Proof. exact (h1). Qed.
Lemma lem4965423 {_113204 : Type'} (x : _113204) (y : _113204) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4965424 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4965425 {_113204 : Type'} : (@eq _113204) = (@eq _113204).
Proof. exact (eq_refl (@eq _113204)). Qed.
Lemma lem4965430 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965432 {_113204 : Type'} (f : _113204 -> _113204) (x : _113204) : (f x) = (@I (_113204 -> _113204) f x).
Proof. exact (@lem4965430 _113204 _113204 f x). Qed.
Lemma lem4965437 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965438 {_113204 : Type'} (f : _113204 -> _113204) (x : _113204) : (f x) = (@I (_113204 -> _113204) f x).
Proof. exact (@lem4965437 _113204 _113204 f x). Qed.
Lemma lem4965440 {_113204 : Type'} (f : _113204 -> _113204) (y : _113204) : (f y) = (@I (_113204 -> _113204) f y).
Proof. exact (@lem4965438 _113204 f y). Qed.
Lemma lem4965441 {_113204 : Type'} (f : _113204 -> _113204) (x : _113204) : (term207 _113204 f x) = (term208 _113204 f x).
Proof. exact (MK_COMB (@lem4965425 _113204) (@lem4965432 _113204 f x)). Qed.
Lemma lem4965442 {_113204 : Type'} (x : _113204) (f : _113204 -> _113204) (y : _113204) : ((f x) = (f y)) = ((@I (_113204 -> _113204) f x) = (@I (_113204 -> _113204) f y)).
Proof. exact (MK_COMB (@lem4965441 _113204 f x) (@lem4965440 _113204 f y)). Qed.
Lemma lem4965443 {_113204 : Type'} (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term209 _113204 x f y) = (term210 _113204 x f y).
Proof. exact (MK_COMB (@lem4965424) (@lem4965442 _113204 x f y)). Qed.
Lemma lem4965444 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4965451 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965452 {_113204 : Type'} (f : type1364 _113204) (x : _113204) : (f x) = (@I (_113204 -> (_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4965451 _113204 (type686 _113204) f x). Qed.
Lemma lem4965453 {_113204 : Type'} (y : _113204) : (@IN _113204 y) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y).
Proof. exact (@lem4965452 _113204 (@IN _113204) y). Qed.
Lemma lem4965454 {_113204 : Type'} (s : _113204 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4965455 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (@IN _113204 y s) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y s).
Proof. exact (MK_COMB (@lem4965453 _113204 y) (@lem4965454 _113204 s)). Qed.
Lemma lem4965457 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965458 {_113204 : Type'} (f : type686 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4965457 (_113204 -> Prop) Prop f x). Qed.
Lemma lem4965459 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y s) = (term211 _113204 y s).
Proof. exact (@lem4965458 _113204 (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y) s). Qed.
Lemma lem4965461 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (@IN _113204 y s) = (term211 _113204 y s).
Proof. exact (TRANS (@lem4965455 _113204 y s) (@lem4965459 _113204 y s)). Qed.
Lemma lem4965462 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (term212 _113204 y s) = (term213 _113204 y s).
Proof. exact (MK_COMB (@lem4965444) (@lem4965461 _113204 y s)). Qed.
Lemma lem4965463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4965464 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (term183 _113204 y s) = (term214 _113204 y s).
Proof. exact (MK_COMB (@lem4965463) (@lem4965462 _113204 y s)). Qed.
Lemma lem4965465 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term182 _113204 s x f y) = (term215 _113204 s x f y).
Proof. exact (MK_COMB (@lem4965464 _113204 y s) (@lem4965443 _113204 x f y)). Qed.
Lemma lem4965466 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4965473 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965474 {_113204 : Type'} (f : type1364 _113204) (x : _113204) : (f x) = (@I (_113204 -> (_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4965473 _113204 (type686 _113204) f x). Qed.
Lemma lem4965475 {_113204 : Type'} (x : _113204) : (@IN _113204 x) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x).
Proof. exact (@lem4965474 _113204 (@IN _113204) x). Qed.
Lemma lem4965476 {_113204 : Type'} (s : _113204 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4965477 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (@IN _113204 x s) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x s).
Proof. exact (MK_COMB (@lem4965475 _113204 x) (@lem4965476 _113204 s)). Qed.
Lemma lem4965479 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965480 {_113204 : Type'} (f : type686 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4965479 (_113204 -> Prop) Prop f x). Qed.
Lemma lem4965481 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x s) = (term211 _113204 x s).
Proof. exact (@lem4965480 _113204 (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x) s). Qed.
Lemma lem4965483 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (@IN _113204 x s) = (term211 _113204 x s).
Proof. exact (TRANS (@lem4965477 _113204 x s) (@lem4965481 _113204 x s)). Qed.
Lemma lem4965484 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (term212 _113204 x s) = (term213 _113204 x s).
Proof. exact (MK_COMB (@lem4965466) (@lem4965483 _113204 x s)). Qed.
Lemma lem4965485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4965486 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (term183 _113204 x s) = (term214 _113204 x s).
Proof. exact (MK_COMB (@lem4965485) (@lem4965484 _113204 x s)). Qed.
Lemma lem4965487 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term185 _113204 s x f y) = (term216 _113204 s x f y).
Proof. exact (MK_COMB (@lem4965486 _113204 x s) (@lem4965465 _113204 s x f y)). Qed.
Lemma lem4965488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4965489 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term189 _113204 s x f y) = (term217 _113204 s x f y).
Proof. exact (MK_COMB (@lem4965488) (@lem4965487 _113204 s x f y)). Qed.
Lemma lem4965490 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term191 _113204 s f x y) = (term218 _113204 s f x y).
Proof. exact (MK_COMB (@lem4965489 _113204 s x f y) (@lem4965423 _113204 x y)). Qed.
Lemma lem4965491 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term192 _113204 s f x) = (term219 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4965490 _113204 s f x y)). Qed.
Lemma lem4965492 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4965493 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term193 _113204 s f x) = (term220 _113204 s f x).
Proof. exact (MK_COMB (@lem4965492 _113204) (@lem4965491 _113204 s f x)). Qed.
Lemma lem4965494 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term194 _113204 s f) = (term221 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4965493 _113204 s f x)). Qed.
Lemma lem4965495 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4965496 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term195 _113204 s f) = (term222 _113204 s f).
Proof. exact (MK_COMB (@lem4965495 _113204) (@lem4965494 _113204 s f)). Qed.
Lemma lem4965497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4965498 {_113204 : Type'} : (@eq (_113204 -> Prop)) = (@eq (_113204 -> Prop)).
Proof. exact (eq_refl (@eq (_113204 -> Prop))). Qed.
Lemma lem4965505 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965506 {_113204 : Type'} (f : type484 _113204) (x : _113204 -> _113204) : (f x) = (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) f x).
Proof. exact (@lem4965505 (_113204 -> _113204) (type672 _113204) f x). Qed.
Lemma lem4965507 {_113204 : Type'} (f : _113204 -> _113204) : (@IMAGE _113204 _113204 f) = (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f).
Proof. exact (@lem4965506 _113204 (@IMAGE _113204 _113204) f). Qed.
Lemma lem4965508 {_113204 : Type'} (s : _113204 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4965509 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (@IMAGE _113204 _113204 f s) = (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f s).
Proof. exact (MK_COMB (@lem4965507 _113204 f) (@lem4965508 _113204 s)). Qed.
Lemma lem4965511 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965512 {_113204 : Type'} (f : type672 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> _113204 -> Prop) f x).
Proof. exact (@lem4965511 (_113204 -> Prop) (_113204 -> Prop) f x). Qed.
Lemma lem4965513 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f s) = (term223 _113204 f s).
Proof. exact (@lem4965512 _113204 (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f) s). Qed.
Lemma lem4965515 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (@IMAGE _113204 _113204 f s) = (term223 _113204 f s).
Proof. exact (TRANS (@lem4965509 _113204 f s) (@lem4965513 _113204 f s)). Qed.
Lemma lem4965516 {_113204 : Type'} (t : _113204 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4965517 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term224 _113204 f s) = (term225 _113204 f s).
Proof. exact (MK_COMB (@lem4965498 _113204) (@lem4965515 _113204 f s)). Qed.
Lemma lem4965518 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : ((@IMAGE _113204 _113204 f s) = t) = ((term223 _113204 f s) = t).
Proof. exact (MK_COMB (@lem4965517 _113204 f s) (@lem4965516 _113204 t)). Qed.
Lemma lem4965519 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term226 _113204 f s t) = (term227 _113204 f s t).
Proof. exact (MK_COMB (@lem4965497) (@lem4965518 _113204 f s t)). Qed.
Lemma lem4965520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4965521 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4965526 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965527 {_113204 : Type'} (f : type687 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> nat) f x).
Proof. exact (@lem4965526 (_113204 -> Prop) nat f x). Qed.
Lemma lem4965529 {_113204 : Type'} (s : _113204 -> Prop) : (@CARD _113204 s) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s).
Proof. exact (@lem4965527 _113204 (@CARD _113204) s). Qed.
Lemma lem4965534 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965535 {_113204 : Type'} (f : type687 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> nat) f x).
Proof. exact (@lem4965534 (_113204 -> Prop) nat f x). Qed.
Lemma lem4965537 {_113204 : Type'} (t : _113204 -> Prop) : (@CARD _113204 t) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) t).
Proof. exact (@lem4965535 _113204 (@CARD _113204) t). Qed.
Lemma lem4965538 {_113204 : Type'} (s : _113204 -> Prop) : (term228 _113204 s) = (term229 _113204 s).
Proof. exact (MK_COMB (@lem4965521) (@lem4965529 _113204 s)). Qed.
Lemma lem4965539 {_113204 : Type'} (s : _113204 -> Prop) (t : _113204 -> Prop) : ((@CARD _113204 s) = (@CARD _113204 t)) = ((@I ((_113204 -> Prop) -> nat) (@CARD _113204) s) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) t)).
Proof. exact (MK_COMB (@lem4965538 _113204 s) (@lem4965537 _113204 t)). Qed.
Lemma lem4965540 {_113204 : Type'} (s : _113204 -> Prop) (t : _113204 -> Prop) : (term230 _113204 s t) = (term231 _113204 s t).
Proof. exact (MK_COMB (@lem4965520) (@lem4965539 _113204 s t)). Qed.
Lemma lem4965541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4965542 {_113204 : Type'} (s : _113204 -> Prop) (t : _113204 -> Prop) : (term232 _113204 s t) = (term233 _113204 s t).
Proof. exact (MK_COMB (@lem4965541) (@lem4965540 _113204 s t)). Qed.
Lemma lem4965543 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term175 _113204 f s t) = (term234 _113204 f s t).
Proof. exact (MK_COMB (@lem4965542 _113204 s t) (@lem4965519 _113204 f s t)). Qed.
Lemma lem4965544 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4965549 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4965550 {_113204 : Type'} (f : type686 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4965549 (_113204 -> Prop) Prop f x). Qed.
Lemma lem4965552 {_113204 : Type'} (s : _113204 -> Prop) : (@FINITE _113204 s) = (@I ((_113204 -> Prop) -> Prop) (@FINITE _113204) s).
Proof. exact (@lem4965550 _113204 (@FINITE _113204) s). Qed.
Lemma lem4965553 {_113204 : Type'} (s : _113204 -> Prop) : (term235 _113204 s) = (term236 _113204 s).
Proof. exact (MK_COMB (@lem4965544) (@lem4965552 _113204 s)). Qed.
Lemma lem4965554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4965555 {_113204 : Type'} (s : _113204 -> Prop) : (term176 _113204 s) = (term237 _113204 s).
Proof. exact (MK_COMB (@lem4965554) (@lem4965553 _113204 s)). Qed.
Lemma lem4965556 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term178 _113204 f s t) = (term238 _113204 f s t).
Proof. exact (MK_COMB (@lem4965555 _113204 s) (@lem4965543 _113204 f s t)). Qed.
Lemma lem4965557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4965558 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term197 _113204 f s t) = (term239 _113204 f s t).
Proof. exact (MK_COMB (@lem4965557) (@lem4965556 _113204 f s t)). Qed.
Lemma lem4965559 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term199 _113204 t s f) = (term240 _113204 t s f).
Proof. exact (MK_COMB (@lem4965558 _113204 f s t) (@lem4965496 _113204 s f)). Qed.
Lemma lem4965560 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term201 _113204 t s) = (term241 _113204 t s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4965559 _113204 t s f)). Qed.
Lemma lem4965561 {_113204 : Type'} : (@all (_113204 -> _113204)) = (@all (_113204 -> _113204)).
Proof. exact (eq_refl (@all (_113204 -> _113204))). Qed.
Lemma lem4965562 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term202 _113204 t s) = (term242 _113204 t s).
Proof. exact (MK_COMB (@lem4965561 _113204) (@lem4965560 _113204 t s)). Qed.
Lemma lem4965563 {_113204 : Type'} (s : _113204 -> Prop) : (term203 _113204 s) = (term243 _113204 s).
Proof. exact (fun_ext (fun t : _113204 -> Prop => @lem4965562 _113204 t s)). Qed.
Lemma lem4965564 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4965565 {_113204 : Type'} (s : _113204 -> Prop) : (term204 _113204 s) = (term244 _113204 s).
Proof. exact (MK_COMB (@lem4965564 _113204) (@lem4965563 _113204 s)). Qed.
Lemma lem4965566 {_113204 : Type'} : (term205 _113204) = (term245 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4965565 _113204 s)). Qed.
Lemma lem4965567 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4965568 {_113204 : Type'} : (term206 _113204) = (term246 _113204).
Proof. exact (MK_COMB (@lem4965567 _113204) (@lem4965566 _113204)). Qed.
Lemma lem4965569 {_113204 : Type'} (h1 : term13 _113204) : term246 _113204.
Proof. exact (EQ_MP (@lem4965568 _113204) (@lem4964754 _113204 h1)). Qed.
Lemma lem4966180 {_113204 : Type'} (x : _113204) (y : _113204) : (term247 _113204 x y) = (term247 _113204 x y).
Proof. exact (eq_refl (term247 _113204 x y)). Qed.
Lemma lem4966181 {_113204 : Type'} : (@eq _113204) = (@eq _113204).
Proof. exact (eq_refl (@eq _113204)). Qed.
Lemma lem4966186 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966188 {_113204 : Type'} (f : _113204 -> _113204) (x : _113204) : (f x) = (@I (_113204 -> _113204) f x).
Proof. exact (@lem4966186 _113204 _113204 f x). Qed.
Lemma lem4966193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966194 {_113204 : Type'} (f : _113204 -> _113204) (x : _113204) : (f x) = (@I (_113204 -> _113204) f x).
Proof. exact (@lem4966193 _113204 _113204 f x). Qed.
Lemma lem4966196 {_113204 : Type'} (f : _113204 -> _113204) (y : _113204) : (f y) = (@I (_113204 -> _113204) f y).
Proof. exact (@lem4966194 _113204 f y). Qed.
Lemma lem4966197 {_113204 : Type'} (f : _113204 -> _113204) (x : _113204) : (term207 _113204 f x) = (term208 _113204 f x).
Proof. exact (MK_COMB (@lem4966181 _113204) (@lem4966188 _113204 f x)). Qed.
Lemma lem4966198 {_113204 : Type'} (x : _113204) (f : _113204 -> _113204) (y : _113204) : ((f x) = (f y)) = ((@I (_113204 -> _113204) f x) = (@I (_113204 -> _113204) f y)).
Proof. exact (MK_COMB (@lem4966197 _113204 f x) (@lem4966196 _113204 f y)). Qed.
Lemma lem4966205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966206 {_113204 : Type'} (f : type1364 _113204) (x : _113204) : (f x) = (@I (_113204 -> (_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4966205 _113204 (type686 _113204) f x). Qed.
Lemma lem4966207 {_113204 : Type'} (y : _113204) : (@IN _113204 y) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y).
Proof. exact (@lem4966206 _113204 (@IN _113204) y). Qed.
Lemma lem4966208 {_113204 : Type'} (s : _113204 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4966209 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (@IN _113204 y s) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y s).
Proof. exact (MK_COMB (@lem4966207 _113204 y) (@lem4966208 _113204 s)). Qed.
Lemma lem4966211 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966212 {_113204 : Type'} (f : type686 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4966211 (_113204 -> Prop) Prop f x). Qed.
Lemma lem4966213 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y s) = (term211 _113204 y s).
Proof. exact (@lem4966212 _113204 (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) y) s). Qed.
Lemma lem4966215 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (@IN _113204 y s) = (term211 _113204 y s).
Proof. exact (TRANS (@lem4966209 _113204 y s) (@lem4966213 _113204 y s)). Qed.
Lemma lem4966216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4966217 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (term248 _113204 y s) = (term249 _113204 y s).
Proof. exact (MK_COMB (@lem4966216) (@lem4966215 _113204 y s)). Qed.
Lemma lem4966218 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term187 _113204 s x f y) = (term250 _113204 s x f y).
Proof. exact (MK_COMB (@lem4966217 _113204 y s) (@lem4966198 _113204 x f y)). Qed.
Lemma lem4966225 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966226 {_113204 : Type'} (f : type1364 _113204) (x : _113204) : (f x) = (@I (_113204 -> (_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4966225 _113204 (type686 _113204) f x). Qed.
Lemma lem4966227 {_113204 : Type'} (x : _113204) : (@IN _113204 x) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x).
Proof. exact (@lem4966226 _113204 (@IN _113204) x). Qed.
Lemma lem4966228 {_113204 : Type'} (s : _113204 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4966229 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (@IN _113204 x s) = (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x s).
Proof. exact (MK_COMB (@lem4966227 _113204 x) (@lem4966228 _113204 s)). Qed.
Lemma lem4966231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966232 {_113204 : Type'} (f : type686 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4966231 (_113204 -> Prop) Prop f x). Qed.
Lemma lem4966233 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x s) = (term211 _113204 x s).
Proof. exact (@lem4966232 _113204 (@I (_113204 -> (_113204 -> Prop) -> Prop) (@IN _113204) x) s). Qed.
Lemma lem4966235 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (@IN _113204 x s) = (term211 _113204 x s).
Proof. exact (TRANS (@lem4966229 _113204 x s) (@lem4966233 _113204 x s)). Qed.
Lemma lem4966236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4966237 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (term248 _113204 x s) = (term249 _113204 x s).
Proof. exact (MK_COMB (@lem4966236) (@lem4966235 _113204 x s)). Qed.
Lemma lem4966238 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term103 _113204 s x f y) = (term251 _113204 s x f y).
Proof. exact (MK_COMB (@lem4966237 _113204 x s) (@lem4966218 _113204 s x f y)). Qed.
Lemma lem4966239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4966240 {_113204 : Type'} (s : _113204 -> Prop) (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term252 _113204 s x f y) = (term253 _113204 s x f y).
Proof. exact (MK_COMB (@lem4966239) (@lem4966238 _113204 s x f y)). Qed.
Lemma lem4966241 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term102 _113204 s f x y) = (term254 _113204 s f x y).
Proof. exact (MK_COMB (@lem4966240 _113204 s x f y) (@lem4966180 _113204 x y)). Qed.
Lemma lem4966242 {_113204 : Type'} : (@eq (_113204 -> Prop)) = (@eq (_113204 -> Prop)).
Proof. exact (eq_refl (@eq (_113204 -> Prop))). Qed.
Lemma lem4966249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966250 {_113204 : Type'} (f : type484 _113204) (x : _113204 -> _113204) : (f x) = (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) f x).
Proof. exact (@lem4966249 (_113204 -> _113204) (type672 _113204) f x). Qed.
Lemma lem4966251 {_113204 : Type'} (f : _113204 -> _113204) : (@IMAGE _113204 _113204 f) = (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f).
Proof. exact (@lem4966250 _113204 (@IMAGE _113204 _113204) f). Qed.
Lemma lem4966252 {_113204 : Type'} (s : _113204 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4966253 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (@IMAGE _113204 _113204 f s) = (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f s).
Proof. exact (MK_COMB (@lem4966251 _113204 f) (@lem4966252 _113204 s)). Qed.
Lemma lem4966255 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966256 {_113204 : Type'} (f : type672 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> _113204 -> Prop) f x).
Proof. exact (@lem4966255 (_113204 -> Prop) (_113204 -> Prop) f x). Qed.
Lemma lem4966257 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f s) = (term223 _113204 f s).
Proof. exact (@lem4966256 _113204 (@I ((_113204 -> _113204) -> (_113204 -> Prop) -> _113204 -> Prop) (@IMAGE _113204 _113204) f) s). Qed.
Lemma lem4966259 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (@IMAGE _113204 _113204 f s) = (term223 _113204 f s).
Proof. exact (TRANS (@lem4966253 _113204 f s) (@lem4966257 _113204 f s)). Qed.
Lemma lem4966260 {_113204 : Type'} (s : _113204 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4966261 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term224 _113204 f s) = (term225 _113204 f s).
Proof. exact (MK_COMB (@lem4966242 _113204) (@lem4966259 _113204 f s)). Qed.
Lemma lem4966262 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : ((@IMAGE _113204 _113204 f s) = s) = ((term223 _113204 f s) = s).
Proof. exact (MK_COMB (@lem4966261 _113204 f s) (@lem4966260 _113204 s)). Qed.
Lemma lem4966267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4966268 {_113204 : Type'} (f : type686 _113204) (x : _113204 -> Prop) : (f x) = (@I ((_113204 -> Prop) -> Prop) f x).
Proof. exact (@lem4966267 (_113204 -> Prop) Prop f x). Qed.
Lemma lem4966270 {_113204 : Type'} (s : _113204 -> Prop) : (@FINITE _113204 s) = (@I ((_113204 -> Prop) -> Prop) (@FINITE _113204) s).
Proof. exact (@lem4966268 _113204 (@FINITE _113204) s). Qed.
Lemma lem4966271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4966272 {_113204 : Type'} (s : _113204 -> Prop) : (term255 _113204 s) = (term256 _113204 s).
Proof. exact (MK_COMB (@lem4966271) (@lem4966270 _113204 s)). Qed.
Lemma lem4966273 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term124 _113204 f s) = (term257 _113204 f s).
Proof. exact (MK_COMB (@lem4966272 _113204 s) (@lem4966262 _113204 f s)). Qed.
Lemma lem4966274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4966275 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term120 _113204 f s) = (term258 _113204 f s).
Proof. exact (MK_COMB (@lem4966274) (@lem4966273 _113204 f s)). Qed.
Lemma lem4966276 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term164 _113204 s f x y) = (term259 _113204 s f x y).
Proof. exact (MK_COMB (@lem4966275 _113204 f s) (@lem4966241 _113204 s f x y)). Qed.
Lemma lem4966277 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term259 _113204 s f x y.
Proof. exact (EQ_MP (@lem4966276 _113204 s f x y) (@lem4965418 _113204 s f x y h1)). Qed.
Lemma lem4966278 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term254 _113204 s f x y.
Proof. exact (proj2 (@lem4966277 _113204 s f x y h1)). Qed.
Lemma lem4966279 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term257 _113204 f s.
Proof. exact (proj1 (@lem4966277 _113204 s f x y h1)). Qed.
Lemma lem4966281 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term251 _113204 s x f y.
Proof. exact (proj1 (@lem4966278 _113204 s f x y h1)). Qed.
Lemma lem4966282 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term250 _113204 s x f y.
Proof. exact (proj2 (@lem4966281 _113204 s f x y h1)). Qed.
Lemma lem4966289 {A : Type'} (P : Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4966290 {_113204 : Type'} (P : Prop) (Q : _113204 -> Prop) : (term260 _113204 P Q) = (term261 _113204 P Q).
Proof. exact (@lem4966289 _113204 P Q). Qed.
Lemma lem4966291 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term262 _113204 t s f) = (term263 _113204 t s f).
Proof. exact (@lem4966290 _113204 (term238 _113204 f s t) (term221 _113204 s f)). Qed.
Lemma lem4966292 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term264 _113204 s f x) = (term220 _113204 s f x).
Proof. exact (eq_refl (term264 _113204 s f x)). Qed.
Lemma lem4966293 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term265 _113204 s f) = (term221 _113204 s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4966292 _113204 s f x)). Qed.
Lemma lem4966294 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4966295 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) : (term266 _113204 s f) = (term222 _113204 s f).
Proof. exact (MK_COMB (@lem4966294 _113204) (@lem4966293 _113204 s f)). Qed.
Lemma lem4966296 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term239 _113204 f s t) = (term239 _113204 f s t).
Proof. exact (eq_refl (term239 _113204 f s t)). Qed.
Lemma lem4966297 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term262 _113204 t s f) = (term240 _113204 t s f).
Proof. exact (MK_COMB (@lem4966296 _113204 f s t) (@lem4966295 _113204 s f)). Qed.
Lemma lem4966298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4966299 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term267 _113204 t s f) = (term268 _113204 t s f).
Proof. exact (MK_COMB (@lem4966298) (@lem4966297 _113204 t s f)). Qed.
Lemma lem4966300 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term264 _113204 s f x) = (term220 _113204 s f x).
Proof. exact (eq_refl (term264 _113204 s f x)). Qed.
Lemma lem4966301 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term239 _113204 f s t) = (term239 _113204 f s t).
Proof. exact (eq_refl (term239 _113204 f s t)). Qed.
Lemma lem4966302 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term269 _113204 t s f x) = (term270 _113204 t s f x).
Proof. exact (MK_COMB (@lem4966301 _113204 f s t) (@lem4966300 _113204 s f x)). Qed.
Lemma lem4966303 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term271 _113204 t s f) = (term272 _113204 t s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4966302 _113204 t s f x)). Qed.
Lemma lem4966304 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4966305 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term263 _113204 t s f) = (term273 _113204 t s f).
Proof. exact (MK_COMB (@lem4966304 _113204) (@lem4966303 _113204 t s f)). Qed.
Lemma lem4966306 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : ((term262 _113204 t s f) = (term263 _113204 t s f)) = ((term240 _113204 t s f) = (term273 _113204 t s f)).
Proof. exact (MK_COMB (@lem4966299 _113204 t s f) (@lem4966305 _113204 t s f)). Qed.
Lemma lem4966307 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term240 _113204 t s f) = (term273 _113204 t s f).
Proof. exact (EQ_MP (@lem4966306 _113204 t s f) (@lem4966291 _113204 t s f)). Qed.
Lemma lem4966309 {A : Type'} (P : Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4966310 {_113204 : Type'} (P : Prop) (Q : _113204 -> Prop) : (term260 _113204 P Q) = (term261 _113204 P Q).
Proof. exact (@lem4966309 _113204 P Q). Qed.
Lemma lem4966311 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term274 _113204 t s f x) = (term275 _113204 t s f x).
Proof. exact (@lem4966310 _113204 (term238 _113204 f s t) (term219 _113204 s f x)). Qed.
Lemma lem4966312 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term276 _113204 s f x y) = (term218 _113204 s f x y).
Proof. exact (eq_refl (term276 _113204 s f x y)). Qed.
Lemma lem4966313 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term277 _113204 s f x) = (term219 _113204 s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4966312 _113204 s f x y)). Qed.
Lemma lem4966314 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4966315 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term278 _113204 s f x) = (term220 _113204 s f x).
Proof. exact (MK_COMB (@lem4966314 _113204) (@lem4966313 _113204 s f x)). Qed.
Lemma lem4966316 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term239 _113204 f s t) = (term239 _113204 f s t).
Proof. exact (eq_refl (term239 _113204 f s t)). Qed.
Lemma lem4966317 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term274 _113204 t s f x) = (term270 _113204 t s f x).
Proof. exact (MK_COMB (@lem4966316 _113204 f s t) (@lem4966315 _113204 s f x)). Qed.
Lemma lem4966318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4966319 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term279 _113204 t s f x) = (term280 _113204 t s f x).
Proof. exact (MK_COMB (@lem4966318) (@lem4966317 _113204 t s f x)). Qed.
Lemma lem4966320 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term276 _113204 s f x y) = (term218 _113204 s f x y).
Proof. exact (eq_refl (term276 _113204 s f x y)). Qed.
Lemma lem4966321 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) (t : _113204 -> Prop) : (term239 _113204 f s t) = (term239 _113204 f s t).
Proof. exact (eq_refl (term239 _113204 f s t)). Qed.
Lemma lem4966322 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term281 _113204 t s f x y) = (term282 _113204 t s f x y).
Proof. exact (MK_COMB (@lem4966321 _113204 f s t) (@lem4966320 _113204 s f x y)). Qed.
Lemma lem4966323 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term283 _113204 t s f x) = (term284 _113204 t s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4966322 _113204 t s f x y)). Qed.
Lemma lem4966324 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4966325 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term275 _113204 t s f x) = (term285 _113204 t s f x).
Proof. exact (MK_COMB (@lem4966324 _113204) (@lem4966323 _113204 t s f x)). Qed.
Lemma lem4966326 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : ((term274 _113204 t s f x) = (term275 _113204 t s f x)) = ((term270 _113204 t s f x) = (term285 _113204 t s f x)).
Proof. exact (MK_COMB (@lem4966319 _113204 t s f x) (@lem4966325 _113204 t s f x)). Qed.
Lemma lem4966327 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term270 _113204 t s f x) = (term285 _113204 t s f x).
Proof. exact (EQ_MP (@lem4966326 _113204 t s f x) (@lem4966311 _113204 t s f x)). Qed.
Lemma lem4966328 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term272 _113204 t s f) = (term286 _113204 t s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4966327 _113204 t s f x)). Qed.
Lemma lem4966329 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4966330 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term273 _113204 t s f) = (term287 _113204 t s f).
Proof. exact (MK_COMB (@lem4966329 _113204) (@lem4966328 _113204 t s f)). Qed.
Lemma lem4966331 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term240 _113204 t s f) = (term287 _113204 t s f).
Proof. exact (TRANS (@lem4966307 _113204 t s f) (@lem4966330 _113204 t s f)). Qed.
Lemma lem4966332 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term241 _113204 t s) = (term288 _113204 t s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4966331 _113204 t s f)). Qed.
Lemma lem4966333 {_113204 : Type'} : (@all (_113204 -> _113204)) = (@all (_113204 -> _113204)).
Proof. exact (eq_refl (@all (_113204 -> _113204))). Qed.
Lemma lem4966334 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term242 _113204 t s) = (term289 _113204 t s).
Proof. exact (MK_COMB (@lem4966333 _113204) (@lem4966332 _113204 t s)). Qed.
Lemma lem4966335 {_113204 : Type'} (s : _113204 -> Prop) : (term243 _113204 s) = (term290 _113204 s).
Proof. exact (fun_ext (fun t : _113204 -> Prop => @lem4966334 _113204 t s)). Qed.
Lemma lem4966336 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4966337 {_113204 : Type'} (s : _113204 -> Prop) : (term244 _113204 s) = (term291 _113204 s).
Proof. exact (MK_COMB (@lem4966336 _113204) (@lem4966335 _113204 s)). Qed.
Lemma lem4966338 {_113204 : Type'} : (term245 _113204) = (term292 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4966337 _113204 s)). Qed.
Lemma lem4966339 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4966340 {_113204 : Type'} : (term246 _113204) = (term293 _113204).
Proof. exact (MK_COMB (@lem4966339 _113204) (@lem4966338 _113204)). Qed.
Lemma lem4966377 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) : (term282 _113204 t s f x y) = (term282 _113204 t s f x y).
Proof. exact (eq_refl (term282 _113204 t s f x y)). Qed.
Lemma lem4966378 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term284 _113204 t s f x) = (term284 _113204 t s f x).
Proof. exact (fun_ext (fun y : _113204 => @lem4966377 _113204 t s f x y)). Qed.
Lemma lem4966379 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4966380 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) : (term285 _113204 t s f x) = (term285 _113204 t s f x).
Proof. exact (MK_COMB (@lem4966379 _113204) (@lem4966378 _113204 t s f x)). Qed.
Lemma lem4966381 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term286 _113204 t s f) = (term286 _113204 t s f).
Proof. exact (fun_ext (fun x : _113204 => @lem4966380 _113204 t s f x)). Qed.
Lemma lem4966382 {_113204 : Type'} : (@all _113204) = (@all _113204).
Proof. exact (eq_refl (@all _113204)). Qed.
Lemma lem4966383 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) (f : _113204 -> _113204) : (term287 _113204 t s f) = (term287 _113204 t s f).
Proof. exact (MK_COMB (@lem4966382 _113204) (@lem4966381 _113204 t s f)). Qed.
Lemma lem4966384 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term288 _113204 t s) = (term288 _113204 t s).
Proof. exact (fun_ext (fun f : _113204 -> _113204 => @lem4966383 _113204 t s f)). Qed.
Lemma lem4966385 {_113204 : Type'} : (@all (_113204 -> _113204)) = (@all (_113204 -> _113204)).
Proof. exact (eq_refl (@all (_113204 -> _113204))). Qed.
Lemma lem4966386 {_113204 : Type'} (t : _113204 -> Prop) (s : _113204 -> Prop) : (term289 _113204 t s) = (term289 _113204 t s).
Proof. exact (MK_COMB (@lem4966385 _113204) (@lem4966384 _113204 t s)). Qed.
Lemma lem4966387 {_113204 : Type'} (s : _113204 -> Prop) : (term290 _113204 s) = (term290 _113204 s).
Proof. exact (fun_ext (fun t : _113204 -> Prop => @lem4966386 _113204 t s)). Qed.
Lemma lem4966388 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4966389 {_113204 : Type'} (s : _113204 -> Prop) : (term291 _113204 s) = (term291 _113204 s).
Proof. exact (MK_COMB (@lem4966388 _113204) (@lem4966387 _113204 s)). Qed.
Lemma lem4966390 {_113204 : Type'} : (term292 _113204) = (term292 _113204).
Proof. exact (fun_ext (fun s : _113204 -> Prop => @lem4966389 _113204 s)). Qed.
Lemma lem4966391 {_113204 : Type'} : (@all (_113204 -> Prop)) = (@all (_113204 -> Prop)).
Proof. exact (eq_refl (@all (_113204 -> Prop))). Qed.
Lemma lem4966392 {_113204 : Type'} : (term293 _113204) = (term293 _113204).
Proof. exact (MK_COMB (@lem4966391 _113204) (@lem4966390 _113204)). Qed.
Lemma lem4966393 {_113204 : Type'} : (term246 _113204) = (term293 _113204).
Proof. exact (TRANS (@lem4966340 _113204) (@lem4966392 _113204)). Qed.
Lemma lem4966394 {_113204 : Type'} (h1 : term13 _113204) : term293 _113204.
Proof. exact (EQ_MP (@lem4966393 _113204) (@lem4965569 _113204 h1)). Qed.
Lemma lem4966847 {_113204 : Type'} (_62383 : _113204 -> Prop) (h1 : term13 _113204) : term294 _113204 _62383.
Proof. exact (@lem4966394 _113204 h1 _62383). Qed.
Lemma lem4966848 {_113204 : Type'} (_62383 : _113204 -> Prop) : (term294 _113204 _62383) = (term291 _113204 _62383).
Proof. exact (eq_refl (term294 _113204 _62383)). Qed.
Lemma lem4966849 {_113204 : Type'} (_62383 : _113204 -> Prop) (h1 : term13 _113204) : term291 _113204 _62383.
Proof. exact (EQ_MP (@lem4966848 _113204 _62383) (@lem4966847 _113204 _62383 h1)). Qed.
Lemma lem4966850 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) (h1 : term13 _113204) : term295 _113204 _62383 _62384.
Proof. exact (@lem4966849 _113204 _62383 h1 _62384). Qed.
Lemma lem4966851 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) : (term295 _113204 _62383 _62384) = (term289 _113204 _62384 _62383).
Proof. exact (eq_refl (term295 _113204 _62383 _62384)). Qed.
Lemma lem4966852 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (h1 : term13 _113204) : term289 _113204 _62384 _62383.
Proof. exact (EQ_MP (@lem4966851 _113204 _62384 _62383) (@lem4966850 _113204 _62383 _62384 h1)). Qed.
Lemma lem4966853 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (h1 : term13 _113204) : term296 _113204 _62384 _62383 _62385.
Proof. exact (@lem4966852 _113204 _62384 _62383 h1 _62385). Qed.
Lemma lem4966854 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) : (term296 _113204 _62384 _62383 _62385) = (term287 _113204 _62384 _62383 _62385).
Proof. exact (eq_refl (term296 _113204 _62384 _62383 _62385)). Qed.
Lemma lem4966855 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (h1 : term13 _113204) : term287 _113204 _62384 _62383 _62385.
Proof. exact (EQ_MP (@lem4966854 _113204 _62384 _62383 _62385) (@lem4966853 _113204 _62384 _62383 _62385 h1)). Qed.
Lemma lem4966856 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (h1 : term13 _113204) : term297 _113204 _62384 _62383 _62385 _62386.
Proof. exact (@lem4966855 _113204 _62384 _62383 _62385 h1 _62386). Qed.
Lemma lem4966857 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) : (term297 _113204 _62384 _62383 _62385 _62386) = (term285 _113204 _62384 _62383 _62385 _62386).
Proof. exact (eq_refl (term297 _113204 _62384 _62383 _62385 _62386)). Qed.
Lemma lem4966858 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (h1 : term13 _113204) : term285 _113204 _62384 _62383 _62385 _62386.
Proof. exact (EQ_MP (@lem4966857 _113204 _62384 _62383 _62385 _62386) (@lem4966856 _113204 _62384 _62383 _62385 _62386 h1)). Qed.
Lemma lem4966859 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (h1 : term13 _113204) : term298 _113204 _62384 _62383 _62385 _62386 _62387.
Proof. exact (@lem4966858 _113204 _62384 _62383 _62385 _62386 h1 _62387). Qed.
Lemma lem4966860 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term298 _113204 _62384 _62383 _62385 _62386 _62387) = (term282 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (eq_refl (term298 _113204 _62384 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966861 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (h1 : term13 _113204) : term282 _113204 _62384 _62383 _62385 _62386 _62387.
Proof. exact (EQ_MP (@lem4966860 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4966859 _113204 _62384 _62383 _62385 _62386 _62387 h1)). Qed.
Lemma lem4966925 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term218 _113204 _62383 _62385 _62386 _62387) = (term299 _113204 _62383 _62385 _62386 _62387).
Proof. exact (@lem4963598 (term213 _113204 _62386 _62383) (term215 _113204 _62383 _62386 _62385 _62387) (_62386 = _62387)). Qed.
Lemma lem4966932 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term300 _113204 _62383 _62385 _62386 _62387) = (term301 _113204 _62383 _62385 _62386 _62387).
Proof. exact (@lem4963598 (term213 _113204 _62387 _62383) (term210 _113204 _62386 _62385 _62387) (_62386 = _62387)). Qed.
Lemma lem4966933 {_113204 : Type'} (_62386 : _113204) (_62383 : _113204 -> Prop) : (term214 _113204 _62386 _62383) = (term214 _113204 _62386 _62383).
Proof. exact (eq_refl (term214 _113204 _62386 _62383)). Qed.
Lemma lem4966936 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term299 _113204 _62383 _62385 _62386 _62387) = (term302 _113204 _62383 _62385 _62386 _62387).
Proof. exact (MK_COMB (@lem4966933 _113204 _62386 _62383) (@lem4966932 _113204 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966938 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term218 _113204 _62383 _62385 _62386 _62387) = (term302 _113204 _62383 _62385 _62386 _62387).
Proof. exact (TRANS (@lem4966925 _113204 _62383 _62385 _62386 _62387) (@lem4966936 _113204 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966939 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term239 _113204 _62385 _62383 _62384) = (term239 _113204 _62385 _62383 _62384).
Proof. exact (eq_refl (term239 _113204 _62385 _62383 _62384)). Qed.
Lemma lem4966940 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term282 _113204 _62384 _62383 _62385 _62386 _62387) = (term303 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (MK_COMB (@lem4966939 _113204 _62385 _62383 _62384) (@lem4966938 _113204 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966941 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term303 _113204 _62384 _62383 _62385 _62386 _62387) = (term304 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (@lem4963598 (term236 _113204 _62383) (term234 _113204 _62385 _62383 _62384) (term302 _113204 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966948 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term305 _113204 _62384 _62383 _62385 _62386 _62387) = (term306 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (@lem4963598 (term231 _113204 _62383 _62384) (term227 _113204 _62385 _62383 _62384) (term302 _113204 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966949 {_113204 : Type'} (_62383 : _113204 -> Prop) : (term237 _113204 _62383) = (term237 _113204 _62383).
Proof. exact (eq_refl (term237 _113204 _62383)). Qed.
Lemma lem4966952 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term304 _113204 _62384 _62383 _62385 _62386 _62387) = (term307 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (MK_COMB (@lem4966949 _113204 _62383) (@lem4966948 _113204 _62384 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966953 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term303 _113204 _62384 _62383 _62385 _62386 _62387) = (term307 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (TRANS (@lem4966941 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4966952 _113204 _62384 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966954 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term282 _113204 _62384 _62383 _62385 _62386 _62387) = (term307 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (TRANS (@lem4966940 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4966953 _113204 _62384 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4966955 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (h1 : term13 _113204) : term307 _113204 _62384 _62383 _62385 _62386 _62387.
Proof. exact (EQ_MP (@lem4966954 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4966861 _113204 _62384 _62383 _62385 _62386 _62387 h1)). Qed.
Lemma lem4967093 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term247 _113204 x y.
Proof. exact (proj2 (@lem4966278 _113204 s f x y h1)). Qed.
Lemma lem4967556 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : @I ((_113204 -> Prop) -> Prop) (@FINITE _113204) s.
Proof. exact (proj1 (@lem4966279 _113204 s f x y h1)). Qed.
Lemma lem4967557 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term308 _113204 s.
Proof. exact (fun h0 : term236 _113204 s => @lem4967556 _113204 s f x y h1). Qed.
Lemma lem4967559 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4967560 {_113204 : Type'} (s : _113204 -> Prop) : (term308 _113204 s) = (@I ((_113204 -> Prop) -> Prop) (@FINITE _113204) s).
Proof. exact (@lem4967559 (@I ((_113204 -> Prop) -> Prop) (@FINITE _113204) s)). Qed.
Lemma lem4967561 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : @I ((_113204 -> Prop) -> Prop) (@FINITE _113204) s.
Proof. exact (EQ_MP (@lem4967560 _113204 s) (@lem4967557 _113204 s f x y h1)). Qed.
Lemma lem4967563 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4967564 {_113204 : Type'} (s : _113204 -> Prop) : (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s).
Proof. exact (@lem4967563 (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s)). Qed.
Lemma lem4967565 {_113204 : Type'} (s : _113204 -> Prop) : term310 _113204 s.
Proof. exact (fun h0 : term311 _113204 s => @lem4967564 _113204 s). Qed.
Lemma lem4967567 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4967568 {_113204 : Type'} (s : _113204 -> Prop) : (term310 _113204 s) = ((@I ((_113204 -> Prop) -> nat) (@CARD _113204) s) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s)).
Proof. exact (@lem4967567 ((@I ((_113204 -> Prop) -> nat) (@CARD _113204) s) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s))). Qed.
Lemma lem4967569 {_113204 : Type'} (s : _113204 -> Prop) : (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) s).
Proof. exact (EQ_MP (@lem4967568 _113204 s) (@lem4967565 _113204 s)). Qed.
Lemma lem4967571 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : (term223 _113204 f s) = s.
Proof. exact (proj2 (@lem4966279 _113204 s f x y h1)). Qed.
Lemma lem4967572 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term312 _113204 f s.
Proof. exact (fun h0 : term313 _113204 f s => @lem4967571 _113204 s f x y h1). Qed.
Lemma lem4967574 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4967575 {_113204 : Type'} (f : _113204 -> _113204) (s : _113204 -> Prop) : (term312 _113204 f s) = ((term223 _113204 f s) = s).
Proof. exact (@lem4967574 ((term223 _113204 f s) = s)). Qed.
Lemma lem4967576 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : (term223 _113204 f s) = s.
Proof. exact (EQ_MP (@lem4967575 _113204 f s) (@lem4967572 _113204 s f x y h1)). Qed.
Lemma lem4967578 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term211 _113204 x s.
Proof. exact (proj1 (@lem4966281 _113204 s f x y h1)). Qed.
Lemma lem4967579 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term314 _113204 x s.
Proof. exact (fun h0 : term213 _113204 x s => @lem4967578 _113204 s f x y h1). Qed.
Lemma lem4967581 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4967582 {_113204 : Type'} (x : _113204) (s : _113204 -> Prop) : (term314 _113204 x s) = (term211 _113204 x s).
Proof. exact (@lem4967581 (term211 _113204 x s)). Qed.
Lemma lem4967583 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term211 _113204 x s.
Proof. exact (EQ_MP (@lem4967582 _113204 x s) (@lem4967579 _113204 s f x y h1)). Qed.
Lemma lem4967585 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term211 _113204 y s.
Proof. exact (proj1 (@lem4966282 _113204 s f x y h1)). Qed.
Lemma lem4967586 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term314 _113204 y s.
Proof. exact (fun h0 : term213 _113204 y s => @lem4967585 _113204 s f x y h1). Qed.
Lemma lem4967588 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4967589 {_113204 : Type'} (y : _113204) (s : _113204 -> Prop) : (term314 _113204 y s) = (term211 _113204 y s).
Proof. exact (@lem4967588 (term211 _113204 y s)). Qed.
Lemma lem4967590 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term211 _113204 y s.
Proof. exact (EQ_MP (@lem4967589 _113204 y s) (@lem4967586 _113204 s f x y h1)). Qed.
Lemma lem4967592 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : (@I (_113204 -> _113204) f x) = (@I (_113204 -> _113204) f y).
Proof. exact (proj2 (@lem4966282 _113204 s f x y h1)). Qed.
Lemma lem4967593 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term315 _113204 x f y.
Proof. exact (fun h0 : term210 _113204 x f y => @lem4967592 _113204 s f x y h1). Qed.
Lemma lem4967595 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4967596 {_113204 : Type'} (x : _113204) (f : _113204 -> _113204) (y : _113204) : (term315 _113204 x f y) = ((@I (_113204 -> _113204) f x) = (@I (_113204 -> _113204) f y)).
Proof. exact (@lem4967595 ((@I (_113204 -> _113204) f x) = (@I (_113204 -> _113204) f y))). Qed.
Lemma lem4967597 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : (@I (_113204 -> _113204) f x) = (@I (_113204 -> _113204) f y).
Proof. exact (EQ_MP (@lem4967596 _113204 x f y) (@lem4967593 _113204 s f x y h1)). Qed.
Lemma lem4967603 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967604 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term307 _113204 _62384 _62383 _62385 _62386 _62387) = (term316 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (@lem4967603 (term231 _113204 _62383 _62384) (term236 _113204 _62383) (term317 _113204 _62384 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4967620 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967621 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term318 _113204 _62384 _62383 _62385 _62386 _62387) = (term319 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (@lem4967620 (term227 _113204 _62385 _62383 _62384) (term236 _113204 _62383) (term302 _113204 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4967657 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967658 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) : (term301 _113204 _62383 _62385 _62386 _62387) = (term320 _113204 _62385 _62383 _62386 _62387).
Proof. exact (@lem4967657 (term210 _113204 _62386 _62385 _62387) (term213 _113204 _62387 _62383) (_62386 = _62387)). Qed.
Lemma lem4967674 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4967675 {_113204 : Type'} (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term321 _113204 _62383 _62386 _62387) = (term322 _113204 _62386 _62387 _62383).
Proof. exact (@lem4967674 (_62386 = _62387) (term213 _113204 _62387 _62383)). Qed.
Lemma lem4967683 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term323 _113204 _62386 _62385 _62387) = (term323 _113204 _62386 _62385 _62387).
Proof. exact (eq_refl (term323 _113204 _62386 _62385 _62387)). Qed.
Lemma lem4967684 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term320 _113204 _62385 _62383 _62386 _62387) = (term324 _113204 _62385 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967683 _113204 _62386 _62385 _62387) (@lem4967675 _113204 _62386 _62387 _62383)). Qed.
Lemma lem4967688 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967689 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term324 _113204 _62385 _62386 _62387 _62383) = (term325 _113204 _62386 _62385 _62387 _62383).
Proof. exact (@lem4967688 (_62386 = _62387) (term210 _113204 _62386 _62385 _62387) (term213 _113204 _62387 _62383)). Qed.
Lemma lem4967709 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term320 _113204 _62385 _62383 _62386 _62387) = (term325 _113204 _62386 _62385 _62387 _62383).
Proof. exact (TRANS (@lem4967684 _113204 _62385 _62386 _62387 _62383) (@lem4967689 _113204 _62386 _62385 _62387 _62383)). Qed.
Lemma lem4967710 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term301 _113204 _62383 _62385 _62386 _62387) = (term325 _113204 _62386 _62385 _62387 _62383).
Proof. exact (TRANS (@lem4967658 _113204 _62385 _62383 _62386 _62387) (@lem4967709 _113204 _62386 _62385 _62387 _62383)). Qed.
Lemma lem4967711 {_113204 : Type'} (_62386 : _113204) (_62383 : _113204 -> Prop) : (term214 _113204 _62386 _62383) = (term214 _113204 _62386 _62383).
Proof. exact (eq_refl (term214 _113204 _62386 _62383)). Qed.
Lemma lem4967712 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term302 _113204 _62383 _62385 _62386 _62387) = (term326 _113204 _62386 _62385 _62387 _62383).
Proof. exact (MK_COMB (@lem4967711 _113204 _62386 _62383) (@lem4967710 _113204 _62386 _62385 _62387 _62383)). Qed.
Lemma lem4967716 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967717 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term326 _113204 _62386 _62385 _62387 _62383) = (term327 _113204 _62386 _62385 _62387 _62383).
Proof. exact (@lem4967716 (_62386 = _62387) (term213 _113204 _62386 _62383) (term328 _113204 _62386 _62385 _62387 _62383)). Qed.
Lemma lem4967733 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967734 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term329 _113204 _62386 _62385 _62387 _62383) = (term330 _113204 _62385 _62386 _62387 _62383).
Proof. exact (@lem4967733 (term210 _113204 _62386 _62385 _62387) (term213 _113204 _62386 _62383) (term213 _113204 _62387 _62383)). Qed.
Lemma lem4967752 {_113204 : Type'} (_62386 : _113204) (_62387 : _113204) : (term331 _113204 _62386 _62387) = (term331 _113204 _62386 _62387).
Proof. exact (eq_refl (term331 _113204 _62386 _62387)). Qed.
Lemma lem4967753 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term327 _113204 _62386 _62385 _62387 _62383) = (term332 _113204 _62385 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967752 _113204 _62386 _62387) (@lem4967734 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967764 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term326 _113204 _62386 _62385 _62387 _62383) = (term332 _113204 _62385 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967717 _113204 _62386 _62385 _62387 _62383) (@lem4967753 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967765 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term302 _113204 _62383 _62385 _62386 _62387) = (term332 _113204 _62385 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967712 _113204 _62386 _62385 _62387 _62383) (@lem4967764 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967766 {_113204 : Type'} (_62383 : _113204 -> Prop) : (term237 _113204 _62383) = (term237 _113204 _62383).
Proof. exact (eq_refl (term237 _113204 _62383)). Qed.
Lemma lem4967767 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term333 _113204 _62383 _62385 _62386 _62387) = (term334 _113204 _62385 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967766 _113204 _62383) (@lem4967765 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967771 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967772 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term334 _113204 _62385 _62386 _62387 _62383) = (term335 _113204 _62385 _62386 _62387 _62383).
Proof. exact (@lem4967771 (_62386 = _62387) (term236 _113204 _62383) (term330 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967788 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967789 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term336 _113204 _62385 _62386 _62387 _62383) = (term337 _113204 _62385 _62386 _62387 _62383).
Proof. exact (@lem4967788 (term210 _113204 _62386 _62385 _62387) (term236 _113204 _62383) (term338 _113204 _62386 _62387 _62383)). Qed.
Lemma lem4967817 {_113204 : Type'} (_62386 : _113204) (_62387 : _113204) : (term331 _113204 _62386 _62387) = (term331 _113204 _62386 _62387).
Proof. exact (eq_refl (term331 _113204 _62386 _62387)). Qed.
Lemma lem4967818 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term335 _113204 _62385 _62386 _62387 _62383) = (term339 _113204 _62385 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967817 _113204 _62386 _62387) (@lem4967789 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967829 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term334 _113204 _62385 _62386 _62387 _62383) = (term339 _113204 _62385 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967772 _113204 _62385 _62386 _62387 _62383) (@lem4967818 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967830 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term333 _113204 _62383 _62385 _62386 _62387) = (term339 _113204 _62385 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967767 _113204 _62385 _62386 _62387 _62383) (@lem4967829 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967831 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term340 _113204 _62385 _62383 _62384) = (term340 _113204 _62385 _62383 _62384).
Proof. exact (eq_refl (term340 _113204 _62385 _62383 _62384)). Qed.
Lemma lem4967832 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term319 _113204 _62384 _62383 _62385 _62386 _62387) = (term341 _113204 _62384 _62385 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967831 _113204 _62385 _62383 _62384) (@lem4967830 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967836 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967837 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term341 _113204 _62384 _62385 _62386 _62387 _62383) = (term342 _113204 _62384 _62385 _62386 _62387 _62383).
Proof. exact (@lem4967836 (_62386 = _62387) (term227 _113204 _62385 _62383 _62384) (term337 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4967853 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967854 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term343 _113204 _62384 _62385 _62386 _62387 _62383) = (term344 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (@lem4967853 (term210 _113204 _62386 _62385 _62387) (term227 _113204 _62385 _62383 _62384) (term345 _113204 _62386 _62387 _62383)). Qed.
Lemma lem4967894 {_113204 : Type'} (_62386 : _113204) (_62387 : _113204) : (term331 _113204 _62386 _62387) = (term331 _113204 _62386 _62387).
Proof. exact (eq_refl (term331 _113204 _62386 _62387)). Qed.
Lemma lem4967895 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term342 _113204 _62384 _62385 _62386 _62387 _62383) = (term346 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967894 _113204 _62386 _62387) (@lem4967854 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4967906 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term341 _113204 _62384 _62385 _62386 _62387 _62383) = (term346 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967837 _113204 _62384 _62385 _62386 _62387 _62383) (@lem4967895 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4967907 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term319 _113204 _62384 _62383 _62385 _62386 _62387) = (term346 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967832 _113204 _62384 _62385 _62386 _62387 _62383) (@lem4967906 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4967908 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term318 _113204 _62384 _62383 _62385 _62386 _62387) = (term346 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967621 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4967907 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4967909 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term233 _113204 _62383 _62384) = (term233 _113204 _62383 _62384).
Proof. exact (eq_refl (term233 _113204 _62383 _62384)). Qed.
Lemma lem4967910 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term316 _113204 _62384 _62383 _62385 _62386 _62387) = (term347 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967909 _113204 _62383 _62384) (@lem4967908 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4967914 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967915 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term347 _113204 _62385 _62384 _62386 _62387 _62383) = (term348 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (@lem4967914 (_62386 = _62387) (term231 _113204 _62383 _62384) (term344 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4967931 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967932 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term349 _113204 _62385 _62384 _62386 _62387 _62383) = (term350 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (@lem4967931 (term210 _113204 _62386 _62385 _62387) (term231 _113204 _62383 _62384) (term351 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4967948 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4967949 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term352 _113204 _62385 _62384 _62386 _62387 _62383) = (term353 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (@lem4967948 (term227 _113204 _62385 _62383 _62384) (term231 _113204 _62383 _62384) (term345 _113204 _62386 _62387 _62383)). Qed.
Lemma lem4967989 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term323 _113204 _62386 _62385 _62387) = (term323 _113204 _62386 _62385 _62387).
Proof. exact (eq_refl (term323 _113204 _62386 _62385 _62387)). Qed.
Lemma lem4967990 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term350 _113204 _62385 _62384 _62386 _62387 _62383) = (term354 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4967989 _113204 _62386 _62385 _62387) (@lem4967949 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968001 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term349 _113204 _62385 _62384 _62386 _62387 _62383) = (term354 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967932 _113204 _62385 _62384 _62386 _62387 _62383) (@lem4967990 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968002 {_113204 : Type'} (_62386 : _113204) (_62387 : _113204) : (term331 _113204 _62386 _62387) = (term331 _113204 _62386 _62387).
Proof. exact (eq_refl (term331 _113204 _62386 _62387)). Qed.
Lemma lem4968003 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term348 _113204 _62385 _62384 _62386 _62387 _62383) = (term355 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4968002 _113204 _62386 _62387) (@lem4968001 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968014 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term347 _113204 _62385 _62384 _62386 _62387 _62383) = (term355 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967915 _113204 _62385 _62384 _62386 _62387 _62383) (@lem4968003 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968015 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term316 _113204 _62384 _62383 _62385 _62386 _62387) = (term355 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967910 _113204 _62385 _62384 _62386 _62387 _62383) (@lem4968014 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968016 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term307 _113204 _62384 _62383 _62385 _62386 _62387) = (term355 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4967604 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4968015 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4968018 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term356 _113204 _62384 _62383 _62385 _62386 _62387) = (term357 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4968017) (@lem4968016 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968034 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4968035 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term358 _113204 _62384 _62383 _62386 _62385 _62387) = (term359 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (@lem4968034 (term231 _113204 _62383 _62384) (term236 _113204 _62383) (term360 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968051 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4968052 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term361 _113204 _62384 _62383 _62386 _62385 _62387) = (term362 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (@lem4968051 (term227 _113204 _62385 _62383 _62384) (term236 _113204 _62383) (term216 _113204 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968088 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4968089 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term215 _113204 _62383 _62386 _62385 _62387) = (term328 _113204 _62386 _62385 _62387 _62383).
Proof. exact (@lem4968088 (term210 _113204 _62386 _62385 _62387) (term213 _113204 _62387 _62383)). Qed.
Lemma lem4968097 {_113204 : Type'} (_62386 : _113204) (_62383 : _113204 -> Prop) : (term214 _113204 _62386 _62383) = (term214 _113204 _62386 _62383).
Proof. exact (eq_refl (term214 _113204 _62386 _62383)). Qed.
Lemma lem4968098 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term216 _113204 _62383 _62386 _62385 _62387) = (term329 _113204 _62386 _62385 _62387 _62383).
Proof. exact (MK_COMB (@lem4968097 _113204 _62386 _62383) (@lem4968089 _113204 _62386 _62385 _62387 _62383)). Qed.
Lemma lem4968102 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4968103 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term329 _113204 _62386 _62385 _62387 _62383) = (term330 _113204 _62385 _62386 _62387 _62383).
Proof. exact (@lem4968102 (term210 _113204 _62386 _62385 _62387) (term213 _113204 _62386 _62383) (term213 _113204 _62387 _62383)). Qed.
Lemma lem4968121 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term216 _113204 _62383 _62386 _62385 _62387) = (term330 _113204 _62385 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4968098 _113204 _62386 _62385 _62387 _62383) (@lem4968103 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4968122 {_113204 : Type'} (_62383 : _113204 -> Prop) : (term237 _113204 _62383) = (term237 _113204 _62383).
Proof. exact (eq_refl (term237 _113204 _62383)). Qed.
Lemma lem4968123 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term363 _113204 _62383 _62386 _62385 _62387) = (term336 _113204 _62385 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4968122 _113204 _62383) (@lem4968121 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4968127 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4968128 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term336 _113204 _62385 _62386 _62387 _62383) = (term337 _113204 _62385 _62386 _62387 _62383).
Proof. exact (@lem4968127 (term210 _113204 _62386 _62385 _62387) (term236 _113204 _62383) (term338 _113204 _62386 _62387 _62383)). Qed.
Lemma lem4968156 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term363 _113204 _62383 _62386 _62385 _62387) = (term337 _113204 _62385 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4968123 _113204 _62385 _62386 _62387 _62383) (@lem4968128 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4968157 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term340 _113204 _62385 _62383 _62384) = (term340 _113204 _62385 _62383 _62384).
Proof. exact (eq_refl (term340 _113204 _62385 _62383 _62384)). Qed.
Lemma lem4968158 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term362 _113204 _62384 _62383 _62386 _62385 _62387) = (term343 _113204 _62384 _62385 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4968157 _113204 _62385 _62383 _62384) (@lem4968156 _113204 _62385 _62386 _62387 _62383)). Qed.
Lemma lem4968162 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4968163 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term343 _113204 _62384 _62385 _62386 _62387 _62383) = (term344 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (@lem4968162 (term210 _113204 _62386 _62385 _62387) (term227 _113204 _62385 _62383 _62384) (term345 _113204 _62386 _62387 _62383)). Qed.
Lemma lem4968203 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term362 _113204 _62384 _62383 _62386 _62385 _62387) = (term344 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4968158 _113204 _62384 _62385 _62386 _62387 _62383) (@lem4968163 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968204 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term361 _113204 _62384 _62383 _62386 _62385 _62387) = (term344 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4968052 _113204 _62384 _62383 _62386 _62385 _62387) (@lem4968203 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968205 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term233 _113204 _62383 _62384) = (term233 _113204 _62383 _62384).
Proof. exact (eq_refl (term233 _113204 _62383 _62384)). Qed.
Lemma lem4968206 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term359 _113204 _62384 _62383 _62386 _62385 _62387) = (term349 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4968205 _113204 _62383 _62384) (@lem4968204 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968210 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4968211 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term349 _113204 _62385 _62384 _62386 _62387 _62383) = (term350 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (@lem4968210 (term210 _113204 _62386 _62385 _62387) (term231 _113204 _62383 _62384) (term351 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968227 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4968228 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term352 _113204 _62385 _62384 _62386 _62387 _62383) = (term353 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (@lem4968227 (term227 _113204 _62385 _62383 _62384) (term231 _113204 _62383 _62384) (term345 _113204 _62386 _62387 _62383)). Qed.
Lemma lem4968268 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term323 _113204 _62386 _62385 _62387) = (term323 _113204 _62386 _62385 _62387).
Proof. exact (eq_refl (term323 _113204 _62386 _62385 _62387)). Qed.
Lemma lem4968269 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term350 _113204 _62385 _62384 _62386 _62387 _62383) = (term354 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4968268 _113204 _62386 _62385 _62387) (@lem4968228 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968280 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term349 _113204 _62385 _62384 _62386 _62387 _62383) = (term354 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4968211 _113204 _62385 _62384 _62386 _62387 _62383) (@lem4968269 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968281 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term359 _113204 _62384 _62383 _62386 _62385 _62387) = (term354 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4968206 _113204 _62385 _62384 _62386 _62387 _62383) (@lem4968280 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968282 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term358 _113204 _62384 _62383 _62386 _62385 _62387) = (term354 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (TRANS (@lem4968035 _113204 _62384 _62383 _62386 _62385 _62387) (@lem4968281 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968283 {_113204 : Type'} (_62386 : _113204) (_62387 : _113204) : (term331 _113204 _62386 _62387) = (term331 _113204 _62386 _62387).
Proof. exact (eq_refl (term331 _113204 _62386 _62387)). Qed.
Lemma lem4968284 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : (term364 _113204 _62384 _62383 _62386 _62385 _62387) = (term355 _113204 _62385 _62384 _62386 _62387 _62383).
Proof. exact (MK_COMB (@lem4968283 _113204 _62386 _62387) (@lem4968282 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968295 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : ((term307 _113204 _62384 _62383 _62385 _62386 _62387) = (term364 _113204 _62384 _62383 _62386 _62385 _62387)) = ((term355 _113204 _62385 _62384 _62386 _62387 _62383) = (term355 _113204 _62385 _62384 _62386 _62387 _62383)).
Proof. exact (MK_COMB (@lem4968018 _113204 _62385 _62384 _62386 _62387 _62383) (@lem4968284 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968297 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4968298 (x : Prop) : (x = x) = True.
Proof. exact (@lem4968297 Prop x). Qed.
Lemma lem4968299 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62384 : _113204 -> Prop) (_62386 : _113204) (_62387 : _113204) (_62383 : _113204 -> Prop) : ((term355 _113204 _62385 _62384 _62386 _62387 _62383) = (term355 _113204 _62385 _62384 _62386 _62387 _62383)) = True.
Proof. exact (@lem4968298 (term355 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968300 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : ((term307 _113204 _62384 _62383 _62385 _62386 _62387) = (term364 _113204 _62384 _62383 _62386 _62385 _62387)) = True.
Proof. exact (TRANS (@lem4968295 _113204 _62385 _62384 _62386 _62387 _62383) (@lem4968299 _113204 _62385 _62384 _62386 _62387 _62383)). Qed.
Lemma lem4968301 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : True = ((term307 _113204 _62384 _62383 _62385 _62386 _62387) = (term364 _113204 _62384 _62383 _62386 _62385 _62387)).
Proof. exact (SYM (@lem4968300 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968302 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term307 _113204 _62384 _62383 _62385 _62386 _62387) = (term364 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (EQ_MP (@lem4968301 _113204 _62384 _62383 _62386 _62385 _62387) (@lem0)). Qed.
Lemma lem4968303 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) (h1 : term13 _113204) : term364 _113204 _62384 _62383 _62386 _62385 _62387.
Proof. exact (EQ_MP (@lem4968302 _113204 _62384 _62383 _62386 _62385 _62387) (@lem4966955 _113204 _62384 _62383 _62385 _62386 _62387 h1)). Qed.
Lemma lem4968305 (b : Prop) (a : Prop) : (a \/ b) = (term365 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4968306 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term364 _113204 _62384 _62383 _62386 _62385 _62387) = (term366 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (@lem4968305 (term358 _113204 _62384 _62383 _62386 _62385 _62387) (_62386 = _62387)). Qed.
Lemma lem4968308 (a : Prop) (b : Prop) : (term367 a b) = (term368 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4968309 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term369 _113204 _62384 _62383 _62386 _62385 _62387) = (term370 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (@lem4968308 (term236 _113204 _62383) (term371 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968311 (a : Prop) : (term372 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4968312 {_113204 : Type'} (_62383 : _113204 -> Prop) : (term373 _113204 _62383) = (@I ((_113204 -> Prop) -> Prop) (@FINITE _113204) _62383).
Proof. exact (@lem4968311 (@I ((_113204 -> Prop) -> Prop) (@FINITE _113204) _62383)). Qed.
Lemma lem4968313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968314 {_113204 : Type'} (_62383 : _113204 -> Prop) : (term374 _113204 _62383) = (term256 _113204 _62383).
Proof. exact (MK_COMB (@lem4968313) (@lem4968312 _113204 _62383)). Qed.
Lemma lem4968316 (a : Prop) (b : Prop) : (term367 a b) = (term368 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4968317 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term375 _113204 _62384 _62383 _62386 _62385 _62387) = (term376 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (@lem4968316 (term231 _113204 _62383 _62384) (term360 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968319 (a : Prop) : (term372 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4968320 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term377 _113204 _62383 _62384) = ((@I ((_113204 -> Prop) -> nat) (@CARD _113204) _62383) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) _62384)).
Proof. exact (@lem4968319 ((@I ((_113204 -> Prop) -> nat) (@CARD _113204) _62383) = (@I ((_113204 -> Prop) -> nat) (@CARD _113204) _62384))). Qed.
Lemma lem4968321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968322 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term378 _113204 _62383 _62384) = (term379 _113204 _62383 _62384).
Proof. exact (MK_COMB (@lem4968321) (@lem4968320 _113204 _62383 _62384)). Qed.
Lemma lem4968324 (a : Prop) (b : Prop) : (term367 a b) = (term368 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4968325 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term380 _113204 _62384 _62383 _62386 _62385 _62387) = (term381 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (@lem4968324 (term227 _113204 _62385 _62383 _62384) (term216 _113204 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968327 (a : Prop) : (term372 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4968328 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term382 _113204 _62385 _62383 _62384) = ((term223 _113204 _62385 _62383) = _62384).
Proof. exact (@lem4968327 ((term223 _113204 _62385 _62383) = _62384)). Qed.
Lemma lem4968329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968330 {_113204 : Type'} (_62385 : _113204 -> _113204) (_62383 : _113204 -> Prop) (_62384 : _113204 -> Prop) : (term383 _113204 _62385 _62383 _62384) = (term384 _113204 _62385 _62383 _62384).
Proof. exact (MK_COMB (@lem4968329) (@lem4968328 _113204 _62385 _62383 _62384)). Qed.
Lemma lem4968332 (a : Prop) (b : Prop) : (term367 a b) = (term368 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4968333 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term385 _113204 _62383 _62386 _62385 _62387) = (term386 _113204 _62383 _62386 _62385 _62387).
Proof. exact (@lem4968332 (term213 _113204 _62386 _62383) (term215 _113204 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968335 (a : Prop) : (term372 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4968336 {_113204 : Type'} (_62386 : _113204) (_62383 : _113204 -> Prop) : (term387 _113204 _62386 _62383) = (term211 _113204 _62386 _62383).
Proof. exact (@lem4968335 (term211 _113204 _62386 _62383)). Qed.
Lemma lem4968337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968338 {_113204 : Type'} (_62386 : _113204) (_62383 : _113204 -> Prop) : (term388 _113204 _62386 _62383) = (term249 _113204 _62386 _62383).
Proof. exact (MK_COMB (@lem4968337) (@lem4968336 _113204 _62386 _62383)). Qed.
Lemma lem4968340 (a : Prop) (b : Prop) : (term367 a b) = (term368 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4968341 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term389 _113204 _62383 _62386 _62385 _62387) = (term390 _113204 _62383 _62386 _62385 _62387).
Proof. exact (@lem4968340 (term213 _113204 _62387 _62383) (term210 _113204 _62386 _62385 _62387)). Qed.
Lemma lem4968343 (a : Prop) : (term372 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4968344 {_113204 : Type'} (_62387 : _113204) (_62383 : _113204 -> Prop) : (term387 _113204 _62387 _62383) = (term211 _113204 _62387 _62383).
Proof. exact (@lem4968343 (term211 _113204 _62387 _62383)). Qed.
Lemma lem4968345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4968346 {_113204 : Type'} (_62387 : _113204) (_62383 : _113204 -> Prop) : (term388 _113204 _62387 _62383) = (term249 _113204 _62387 _62383).
Proof. exact (MK_COMB (@lem4968345) (@lem4968344 _113204 _62387 _62383)). Qed.
Lemma lem4968348 (a : Prop) : (term372 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4968349 {_113204 : Type'} (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term391 _113204 _62386 _62385 _62387) = ((@I (_113204 -> _113204) _62385 _62386) = (@I (_113204 -> _113204) _62385 _62387)).
Proof. exact (@lem4968348 ((@I (_113204 -> _113204) _62385 _62386) = (@I (_113204 -> _113204) _62385 _62387))). Qed.
Lemma lem4968350 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term390 _113204 _62383 _62386 _62385 _62387) = (term250 _113204 _62383 _62386 _62385 _62387).
Proof. exact (MK_COMB (@lem4968346 _113204 _62387 _62383) (@lem4968349 _113204 _62386 _62385 _62387)). Qed.
Lemma lem4968351 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term389 _113204 _62383 _62386 _62385 _62387) = (term250 _113204 _62383 _62386 _62385 _62387).
Proof. exact (TRANS (@lem4968341 _113204 _62383 _62386 _62385 _62387) (@lem4968350 _113204 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968352 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term386 _113204 _62383 _62386 _62385 _62387) = (term251 _113204 _62383 _62386 _62385 _62387).
Proof. exact (MK_COMB (@lem4968338 _113204 _62386 _62383) (@lem4968351 _113204 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968353 {_113204 : Type'} (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term385 _113204 _62383 _62386 _62385 _62387) = (term251 _113204 _62383 _62386 _62385 _62387).
Proof. exact (TRANS (@lem4968333 _113204 _62383 _62386 _62385 _62387) (@lem4968352 _113204 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968354 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term381 _113204 _62384 _62383 _62386 _62385 _62387) = (term392 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (MK_COMB (@lem4968330 _113204 _62385 _62383 _62384) (@lem4968353 _113204 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968355 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term380 _113204 _62384 _62383 _62386 _62385 _62387) = (term392 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (TRANS (@lem4968325 _113204 _62384 _62383 _62386 _62385 _62387) (@lem4968354 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968356 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term376 _113204 _62384 _62383 _62386 _62385 _62387) = (term393 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (MK_COMB (@lem4968322 _113204 _62383 _62384) (@lem4968355 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968357 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term375 _113204 _62384 _62383 _62386 _62385 _62387) = (term393 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (TRANS (@lem4968317 _113204 _62384 _62383 _62386 _62385 _62387) (@lem4968356 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968358 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term370 _113204 _62384 _62383 _62386 _62385 _62387) = (term394 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (MK_COMB (@lem4968314 _113204 _62383) (@lem4968357 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968359 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term369 _113204 _62384 _62383 _62386 _62385 _62387) = (term394 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (TRANS (@lem4968309 _113204 _62384 _62383 _62386 _62385 _62387) (@lem4968358 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4968361 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62386 : _113204) (_62385 : _113204 -> _113204) (_62387 : _113204) : (term395 _113204 _62384 _62383 _62386 _62385 _62387) = (term396 _113204 _62384 _62383 _62386 _62385 _62387).
Proof. exact (MK_COMB (@lem4968360) (@lem4968359 _113204 _62384 _62383 _62386 _62385 _62387)). Qed.
Lemma lem4968362 {_113204 : Type'} (_62386 : _113204) (_62387 : _113204) : (_62386 = _62387) = (_62386 = _62387).
Proof. exact (eq_refl (_62386 = _62387)). Qed.
Lemma lem4968363 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term366 _113204 _62384 _62383 _62385 _62386 _62387) = (term397 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (MK_COMB (@lem4968361 _113204 _62384 _62383 _62386 _62385 _62387) (@lem4968362 _113204 _62386 _62387)). Qed.
Lemma lem4968364 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) : (term364 _113204 _62384 _62383 _62386 _62385 _62387) = (term397 _113204 _62384 _62383 _62385 _62386 _62387).
Proof. exact (TRANS (@lem4968306 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4968363 _113204 _62384 _62383 _62385 _62386 _62387)). Qed.
Lemma lem4968366 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term250 _113204 s x f y.
Proof. exact (conj (@lem4967590 _113204 s f x y h1) (@lem4967597 _113204 s f x y h1)). Qed.
Lemma lem4968367 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term251 _113204 s x f y.
Proof. exact (conj (@lem4967583 _113204 s f x y h1) (@lem4968366 _113204 s f x y h1)). Qed.
Lemma lem4968368 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term398 _113204 s x f y.
Proof. exact (conj (@lem4967576 _113204 s f x y h1) (@lem4968367 _113204 s f x y h1)). Qed.
Lemma lem4968369 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term399 _113204 s x f y.
Proof. exact (conj (@lem4967569 _113204 s) (@lem4968368 _113204 s f x y h1)). Qed.
Lemma lem4968370 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term400 _113204 s x f y.
Proof. exact (conj (@lem4967561 _113204 s f x y h1) (@lem4968369 _113204 s f x y h1)). Qed.
Lemma lem4968372 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (h1 : term13 _113204) : term397 _113204 _62384 _62383 _62385 _62386 _62387.
Proof. exact (EQ_MP (@lem4968364 _113204 _62384 _62383 _62385 _62386 _62387) (@lem4968303 _113204 _62384 _62383 _62386 _62385 _62387 h1)). Qed.
Lemma lem4968373 {_113204 : Type'} (_62384 : _113204 -> Prop) (_62383 : _113204 -> Prop) (_62385 : _113204 -> _113204) (_62386 : _113204) (_62387 : _113204) (h1 : term13 _113204) : term397 _113204 _62384 _62383 _62385 _62386 _62387.
Proof. exact (@lem4968372 _113204 _62384 _62383 _62385 _62386 _62387 h1). Qed.
Lemma lem4968374 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term13 _113204) : term401 _113204 s f x y.
Proof. exact (@lem4968373 _113204 s s f x y h1). Qed.
Lemma lem4968377 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term13 _113204) (h2 : term164 _113204 s f x y) : x = y.
Proof. exact (@lem4968374 _113204 s f x y h1 (@lem4968370 _113204 s f x y h2)). Qed.
Lemma lem4968378 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term13 _113204) (h2 : term164 _113204 s f x y) : term402 _113204 x y.
Proof. exact (fun h0 : term247 _113204 x y => @lem4968377 _113204 s f x y h1 h2). Qed.
Lemma lem4968380 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4968381 {_113204 : Type'} (x : _113204) (y : _113204) : (term402 _113204 x y) = (x = y).
Proof. exact (@lem4968380 (x = y)). Qed.
Lemma lem4968382 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term13 _113204) (h2 : term164 _113204 s f x y) : x = y.
Proof. exact (EQ_MP (@lem4968381 _113204 x y) (@lem4968378 _113204 s f x y h1 h2)). Qed.
Lemma lem4968385 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4968387 {_113204 : Type'} (x : _113204) (y : _113204) : (term247 _113204 x y) = (term403 _113204 x y).
Proof. exact (@lem4968385 (x = y)). Qed.
Lemma lem4968390 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term164 _113204 s f x y) : term403 _113204 x y.
Proof. exact (EQ_MP (@lem4968387 _113204 x y) (@lem4967093 _113204 s f x y h1)). Qed.
Lemma lem4968393 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term13 _113204) (h2 : term164 _113204 s f x y) : False.
Proof. exact (@lem4968390 _113204 s f x y h2 (@lem4968382 _113204 s f x y h1 h2)). Qed.
Lemma lem4968394 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term13 _113204) (h2 : term164 _113204 s f x y) : term404.
Proof. exact (fun h0 : ~ False => @lem4968393 _113204 s f x y h1 h2). Qed.
Lemma lem4968396 (p : Prop) : (term309 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4968397 : term404 = False.
Proof. exact (@lem4968396 False). Qed.
Lemma lem4968398 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (y : _113204) (h1 : term13 _113204) (h2 : term164 _113204 s f x y) : False.
Proof. exact (EQ_MP (@lem4968397) (@lem4968394 _113204 s f x y h1 h2)). Qed.
Lemma lem4968399 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (x : _113204) (h1 : term13 _113204) (h2 : term167 _113204 s f x) : False.
Proof. exact (ex_elim (@lem4965417 _113204 s f x h2) (fun y : _113204 => fun h0 : term166 _113204 s f x y => @lem4968398 _113204 s f x y h1 h0)). Qed.
Lemma lem4968400 {_113204 : Type'} (s : _113204 -> Prop) (f : _113204 -> _113204) (h1 : term13 _113204) (h2 : term169 _113204 s f) : False.
Proof. exact (ex_elim (@lem4965416 _113204 s f h2) (fun x : _113204 => fun h0 : term168 _113204 s f x => @lem4968399 _113204 s f x h1 h0)). Qed.
Lemma lem4968401 {_113204 : Type'} (s : _113204 -> Prop) (h1 : term13 _113204) (h2 : term171 _113204 s) : False.
Proof. exact (ex_elim (@lem4965415 _113204 s h2) (fun f : _113204 -> _113204 => fun h0 : term170 _113204 s f => @lem4968400 _113204 s f h1 h0)). Qed.
Lemma lem4968402 {_113204 : Type'} (h1 : term13 _113204) (h2 : term10 _113204) : False.
Proof. exact (ex_elim (@lem4964589 _113204 h2) (fun s : _113204 -> Prop => fun h0 : term172 _113204 s => @lem4968401 _113204 s h1 h0)). Qed.
Lemma lem4968403 {_113204 B : Type'} (h1 : term13 _113204) (h2 : term10 _113204) : term20 _113204 B.
Proof. exact (fun h0 : term15 _113204 B => @lem4968402 _113204 h1 h2). Qed.
Lemma lem4968404 {_113204 B : Type'} : (term20 _113204 B) = (term21 _113204 B).
Proof. exact (@lem69 (term15 _113204 B)). Qed.
Lemma lem4968405 {_113204 B : Type'} (h1 : term13 _113204) (h2 : term10 _113204) : term21 _113204 B.
Proof. exact (EQ_MP (@lem4968404 _113204 B) (@lem4968403 _113204 B h1 h2)). Qed.
Lemma lem4968406 {_113204 A B : Type'} (h1 : term13 _113204) (h2 : term10 _113204) : term24 _113204 A B.
Proof. exact (fun h0 : term14 _113204 A => @lem4968405 _113204 B h1 h2). Qed.
Lemma lem4968407 {_113204 A B : Type'} (h1 : term13 _113204) (h2 : term10 _113204) : term27 _113204 A B.
Proof. exact (fun h0 : term12 _113204 A => @lem4968406 _113204 A B h1 h2). Qed.
Lemma lem4968408 {_113204 A B : Type'} (h1 : term13 _113204) (h2 : term10 _113204) : term30 _113204 A B.
Proof. exact (fun h0 : term11 _113204 B => @lem4968407 _113204 A B h1 h2). Qed.
Lemma lem4968409 {_113204 A B : Type'} (h1 : term10 _113204) : term33 _113204 A B.
Proof. exact (fun h0 : term13 _113204 => @lem4968408 _113204 A B h0 h1). Qed.
Lemma lem4968410 {_113204 A B : Type'} : term35 _113204 A B.
Proof. exact (fun h0 : term10 _113204 => @lem4968409 _113204 A B h0). Qed.
Lemma lem4968411 {_113204 A B : Type'} : term16 _113204 A B.
Proof. exact (EQ_MP (@lem4964360 _113204 A B) (@lem4968410 _113204 A B)). Qed.
Lemma lem4968413 {_113204 A B : Type'} : term16 _113204 A B.
Proof. exact (@lem4963627 _113204 A B (@lem4968411 _113204 A B)). Qed.
Lemma lem4968414 {_113204 A B : Type'} (h1 : term10 _113204) : term32 _113204 A B.
Proof. exact (@lem4968413 _113204 A B (@lem4963603 _113204 h1)). Qed.
Lemma lem4968415 {_113204 A B : Type'} (h1 : term10 _113204) : term29 _113204 A B.
Proof. exact (@lem4968414 _113204 A B h1 (@lem4963606 _113204)). Qed.
Lemma lem4968416 {_113204 A B : Type'} (h1 : term10 _113204) : term26 _113204 A B.
Proof. exact (@lem4968415 _113204 A B h1 (@lem4963604 _113204 B)). Qed.
Lemma lem4968417 {_113204 A B : Type'} (h1 : term10 _113204) : term23 _113204 A B.
Proof. exact (@lem4968416 _113204 A B h1 (@lem4963605 _113204 A)). Qed.
Lemma lem4968418 {_113204 B : Type'} (h1 : term10 _113204) : term20 _113204 B.
Proof. exact (@lem4968417 _113204 Prop B h1 (@lem4963608 _113204 Prop)). Qed.
Lemma lem4968419 {_113204 : Type'} (h1 : term10 _113204) : False.
Proof. exact (@lem4968418 _113204 Prop h1 (@lem4963610 _113204 Prop)). Qed.
Lemma lem4968420 {_113204 : Type'} (h1 : term10 _113204) : (term10 _113204) = False.
Proof. exact (prop_ext (fun h2 : term10 _113204 => @lem4968419 _113204 h1) (fun h2 : False => @lem4963603 _113204 h1)). Qed.
Lemma lem4968421 {_113204 : Type'} (h1 : term10 _113204) : False.
Proof. exact (EQ_MP (@lem4968420 _113204 h1) (@lem4963603 _113204 h1)). Qed.
Lemma lem4968422 {_113204 : Type'} : term9 _113204.
Proof. exact (fun h0 : term10 _113204 => @lem4968421 _113204 h0). Qed.
Lemma lem4968423 {_113204 : Type'} : term8 _113204.
Proof. exact (EQ_MP (@lem4963602 _113204) (@lem4968422 _113204)). Qed.
