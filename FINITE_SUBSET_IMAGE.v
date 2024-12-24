Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUBSET_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import FORALL_FINITE_SUBSET_IMAGE_spec.
Require Import IMAGE_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18394_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
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
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem3694581 {_93870 _93890 : Type'} (P : type686 _93890) : term0 _93870 _93890 P.
Proof. exact (@lem3694570 _93870 _93890 P). Qed.
Lemma lem3694582 {_93870 _93890 : Type'} (P : type686 _93890) : (term0 _93870 _93890 P) = (term1 _93870 _93890 P).
Proof. exact (eq_refl (term0 _93870 _93890 P)). Qed.
Lemma lem3694583 {_93870 _93890 : Type'} (P : type686 _93890) : term1 _93870 _93890 P.
Proof. exact (EQ_MP (@lem3694582 _93870 _93890 P) (@lem3694581 _93870 _93890 P)). Qed.
Lemma lem3694584 {_93870 _93890 : Type'} (P : type686 _93890) (f : _93870 -> _93890) : term2 _93870 _93890 P f.
Proof. exact (@lem3694583 _93870 _93890 P f). Qed.
Lemma lem3694585 {_93870 _93890 : Type'} (P : type686 _93890) (f : _93870 -> _93890) : (term2 _93870 _93890 P f) = (term3 _93870 _93890 P f).
Proof. exact (eq_refl (term2 _93870 _93890 P f)). Qed.
Lemma lem3694586 {_93870 _93890 : Type'} (P : type686 _93890) (f : _93870 -> _93890) : term3 _93870 _93890 P f.
Proof. exact (EQ_MP (@lem3694585 _93870 _93890 P f) (@lem3694584 _93870 _93890 P f)). Qed.
Lemma lem3694587 {_93870 _93890 : Type'} (P : type686 _93890) (f : _93870 -> _93890) (s : _93870 -> Prop) : term4 _93870 _93890 P f s.
Proof. exact (@lem3694586 _93870 _93890 P f s). Qed.
Lemma lem3694588 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term4 _93870 _93890 P f s) = ((term5 _93870 _93890 f s P) = (term6 _93870 _93890 s P f)).
Proof. exact (eq_refl (term4 _93870 _93890 P f s)). Qed.
Lemma lem3694601 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3694602 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term8 A B t f s) = (term9 A B t f s).
Proof. exact (@lem3694601 (term8 A B t f s)). Qed.
Lemma lem3694603 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term9 A B t f s) = (term8 A B t f s).
Proof. exact (SYM (@lem3694602 A B t f s)). Qed.
Lemma lem3694604 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term10 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3694605 {A B : Type'} : term11 A B.
Proof. exact (@lem3615104 A B). Qed.
Lemma lem3694606 {B : Type'} : term12 B.
Proof. exact (@lem3615104 B B). Qed.
Lemma lem3694607 {A : Type'} : term12 A.
Proof. exact (@lem3615104 A A). Qed.
Lemma lem3694610 {_87604 A : Type'} : term13 _87604 A.
Proof. exact (@lem3371475 A _87604). Qed.
Lemma lem3694611 {_87604 B : Type'} : term13 _87604 B.
Proof. exact (@lem3371475 B _87604). Qed.
Lemma lem3694612 {_87593 A : Type'} : term14 _87593 A.
Proof. exact (@lem3371475 _87593 A). Qed.
Lemma lem3694613 {_87593 B : Type'} : term14 _87593 B.
Proof. exact (@lem3371475 _87593 B). Qed.
Lemma lem3694614 {A B : Type'} : term14 A B.
Proof. exact (@lem3371475 A B). Qed.
Lemma lem3694615 {B : Type'} : term15 B.
Proof. exact (@lem3371475 B B). Qed.
Lemma lem3694616 {A : Type'} : term15 A.
Proof. exact (@lem3371475 A A). Qed.
Lemma lem3694619 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term16 _87593 _87604 A B t f s) : term16 _87593 _87604 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3694620 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term17 _87593 _87604 A B t f s.
Proof. exact (fun h0 : term16 _87593 _87604 A B t f s => @lem3694619 _87593 _87604 A B t f s h0). Qed.
Lemma lem3694621 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term17 _87593 _87604 A B t f s) : term17 _87593 _87604 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3694622 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term16 _87593 _87604 A B t f s) : term16 _87593 _87604 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3694623 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term16 _87593 _87604 A B t f s) (h2 : term17 _87593 _87604 A B t f s) : term16 _87593 _87604 A B t f s.
Proof. exact (@lem3694621 _87593 _87604 A B t f s h2 (@lem3694622 _87593 _87604 A B t f s h1)). Qed.
Lemma lem3694624 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term16 _87593 _87604 A B t f s) : term18 _87593 _87604 A B t f s.
Proof. exact (fun h0 : term17 _87593 _87604 A B t f s => @lem3694623 _87593 _87604 A B t f s h1 h0). Qed.
Lemma lem3694625 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term17 _87593 _87604 A B t f s) : term17 _87593 _87604 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3694626 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term16 _87593 _87604 A B t f s) (h2 : term17 _87593 _87604 A B t f s) : term16 _87593 _87604 A B t f s.
Proof. exact (@lem3694624 _87593 _87604 A B t f s h1 (@lem3694625 _87593 _87604 A B t f s h2)). Qed.
Lemma lem3694627 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term17 _87593 _87604 A B t f s) : term17 _87593 _87604 A B t f s.
Proof. exact (fun h0 : term16 _87593 _87604 A B t f s => @lem3694626 _87593 _87604 A B t f s h0 h1). Qed.
Lemma lem3694628 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term19 _87593 _87604 A B t f s.
Proof. exact (fun h0 : term17 _87593 _87604 A B t f s => @lem3694627 _87593 _87604 A B t f s h0). Qed.
Lemma lem3694631 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term17 _87593 _87604 A B t f s.
Proof. exact (@lem3694628 _87593 _87604 A B t f s (@lem3694620 _87593 _87604 A B t f s)). Qed.
Lemma lem3694632 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term17 _87593 _87604 A B t f s.
Proof. exact (@lem3694631 _87593 _87604 A B t f s). Qed.
Lemma lem3694820 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3694821 {B : Type'} : (term20 B) = (term21 B).
Proof. exact (@lem3694820 (term12 B)). Qed.
Lemma lem3694832 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem3694833 {A B : Type'} : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem3694832 A B) (@lem3694821 B)). Qed.
Lemma lem3694836 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem3694837 {A B : Type'} : (term26 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem3694836 A) (@lem3694833 A B)). Qed.
Lemma lem3694840 {B : Type'} : (term28 B) = (term28 B).
Proof. exact (eq_refl (term28 B)). Qed.
Lemma lem3694841 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3694840 B) (@lem3694837 A B)). Qed.
Lemma lem3694844 {_87604 B : Type'} : (term31 _87604 B) = (term31 _87604 B).
Proof. exact (eq_refl (term31 _87604 B)). Qed.
Lemma lem3694845 {_87604 A B : Type'} : (term32 _87604 A B) = (term33 _87604 A B).
Proof. exact (MK_COMB (@lem3694844 _87604 B) (@lem3694841 A B)). Qed.
Lemma lem3694848 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (eq_refl (term34 A B)). Qed.
Lemma lem3694849 {_87604 A B : Type'} : (term35 _87604 A B) = (term36 _87604 A B).
Proof. exact (MK_COMB (@lem3694848 A B) (@lem3694845 _87604 A B)). Qed.
Lemma lem3694852 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem3694853 {_87604 A B : Type'} : (term37 _87604 A B) = (term38 _87604 A B).
Proof. exact (MK_COMB (@lem3694852 A) (@lem3694849 _87604 A B)). Qed.
Lemma lem3694856 {_87604 A : Type'} : (term31 _87604 A) = (term31 _87604 A).
Proof. exact (eq_refl (term31 _87604 A)). Qed.
Lemma lem3694857 {_87604 A B : Type'} : (term39 _87604 A B) = (term40 _87604 A B).
Proof. exact (MK_COMB (@lem3694856 _87604 A) (@lem3694853 _87604 A B)). Qed.
Lemma lem3694860 {_87593 B : Type'} : (term34 _87593 B) = (term34 _87593 B).
Proof. exact (eq_refl (term34 _87593 B)). Qed.
Lemma lem3694861 {_87593 _87604 A B : Type'} : (term41 _87593 _87604 A B) = (term42 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3694860 _87593 B) (@lem3694857 _87604 A B)). Qed.
Lemma lem3694864 {_87593 A : Type'} : (term34 _87593 A) = (term34 _87593 A).
Proof. exact (eq_refl (term34 _87593 A)). Qed.
Lemma lem3694865 {_87593 _87604 A B : Type'} : (term43 _87593 _87604 A B) = (term44 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3694864 _87593 A) (@lem3694861 _87593 _87604 A B)). Qed.
Lemma lem3694868 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term45 A B t f s) = (term45 A B t f s).
Proof. exact (eq_refl (term45 A B t f s)). Qed.
Lemma lem3694869 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term16 _87593 _87604 A B t f s) = (term46 _87593 _87604 A B t f s).
Proof. exact (MK_COMB (@lem3694868 A B t f s) (@lem3694865 _87593 _87604 A B)). Qed.
Lemma lem3694872 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) : (term47 _87593 _87604 A B f s) = (term48 _87593 _87604 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3694869 _87593 _87604 A B t f s)). Qed.
Lemma lem3694873 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3694874 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) : (term49 _87593 _87604 A B f s) = (term50 _87593 _87604 A B f s).
Proof. exact (MK_COMB (@lem3694873 B) (@lem3694872 _87593 _87604 A B f s)). Qed.
Lemma lem3694879 {_87593 _87604 A B : Type'} (s : A -> Prop) : (term51 _87593 _87604 A B s) = (term52 _87593 _87604 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3694874 _87593 _87604 A B f s)). Qed.
Lemma lem3694880 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3694881 {_87593 _87604 A B : Type'} (s : A -> Prop) : (term53 _87593 _87604 A B s) = (term54 _87593 _87604 A B s).
Proof. exact (MK_COMB (@lem3694880 A B) (@lem3694879 _87593 _87604 A B s)). Qed.
Lemma lem3694886 {_87593 _87604 A B : Type'} : (term55 _87593 _87604 A B) = (term56 _87593 _87604 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3694881 _87593 _87604 A B s)). Qed.
Lemma lem3694887 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3694896 {_87593 _87604 A B : Type'} : (term57 _87593 _87604 A B) = (term58 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3694887 A) (@lem3694886 _87593 _87604 A B)). Qed.
Lemma lem3694901 {B : Type'} (f : B -> B) (s : B -> Prop) : (term59 B f s) = (term59 B f s).
Proof. exact (eq_refl (term59 B f s)). Qed.
Lemma lem3694902 {B : Type'} (f : B -> B) : (term60 B f) = (term60 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3694901 B f s)). Qed.
Lemma lem3694903 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3694904 {B : Type'} (f : B -> B) : (term61 B f) = (term61 B f).
Proof. exact (MK_COMB (@lem3694903 B) (@lem3694902 B f)). Qed.
Lemma lem3694905 {B : Type'} : (term62 B) = (term62 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3694904 B f)). Qed.
Lemma lem3694906 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3694907 {B : Type'} : (term12 B) = (term12 B).
Proof. exact (MK_COMB (@lem3694906 B) (@lem3694905 B)). Qed.
Lemma lem3694908 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3694909 {B : Type'} : (term21 B) = (term21 B).
Proof. exact (MK_COMB (@lem3694908) (@lem3694907 B)). Qed.
Lemma lem3694914 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term63 A B f s) = (term63 A B f s).
Proof. exact (eq_refl (term63 A B f s)). Qed.
Lemma lem3694915 {A B : Type'} (f : A -> B) : (term64 A B f) = (term64 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3694914 A B f s)). Qed.
Lemma lem3694916 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3694917 {A B : Type'} (f : A -> B) : (term65 A B f) = (term65 A B f).
Proof. exact (MK_COMB (@lem3694916 A) (@lem3694915 A B f)). Qed.
Lemma lem3694918 {A B : Type'} : (term66 A B) = (term66 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3694917 A B f)). Qed.
Lemma lem3694919 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3694920 {A B : Type'} : (term11 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem3694919 A B) (@lem3694918 A B)). Qed.
Lemma lem3694921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3694922 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem3694921) (@lem3694920 A B)). Qed.
Lemma lem3694923 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem3694922 A B) (@lem3694909 B)). Qed.
Lemma lem3694928 {A : Type'} (f : A -> A) (s : A -> Prop) : (term59 A f s) = (term59 A f s).
Proof. exact (eq_refl (term59 A f s)). Qed.
Lemma lem3694929 {A : Type'} (f : A -> A) : (term60 A f) = (term60 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3694928 A f s)). Qed.
Lemma lem3694930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3694931 {A : Type'} (f : A -> A) : (term61 A f) = (term61 A f).
Proof. exact (MK_COMB (@lem3694930 A) (@lem3694929 A f)). Qed.
Lemma lem3694932 {A : Type'} : (term62 A) = (term62 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3694931 A f)). Qed.
Lemma lem3694933 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3694934 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3694933 A) (@lem3694932 A)). Qed.
Lemma lem3694935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3694936 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem3694935) (@lem3694934 A)). Qed.
Lemma lem3694937 {A B : Type'} : (term27 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem3694936 A) (@lem3694923 A B)). Qed.
Lemma lem3694942 {B : Type'} (s : B -> Prop) (f : B -> B) (t : B -> Prop) : (term67 B s f t) = (term67 B s f t).
Proof. exact (eq_refl (term67 B s f t)). Qed.
Lemma lem3694943 {B : Type'} (s : B -> Prop) (f : B -> B) : (term68 B s f) = (term68 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3694942 B s f t)). Qed.
Lemma lem3694944 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3694945 {B : Type'} (s : B -> Prop) (f : B -> B) : (term69 B s f) = (term69 B s f).
Proof. exact (MK_COMB (@lem3694944 B) (@lem3694943 B s f)). Qed.
Lemma lem3694946 {B : Type'} (f : B -> B) : (term70 B f) = (term70 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3694945 B s f)). Qed.
Lemma lem3694947 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3694948 {B : Type'} (f : B -> B) : (term71 B f) = (term71 B f).
Proof. exact (MK_COMB (@lem3694947 B) (@lem3694946 B f)). Qed.
Lemma lem3694949 {B : Type'} : (term72 B) = (term72 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3694948 B f)). Qed.
Lemma lem3694950 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3694951 {B : Type'} : (term15 B) = (term15 B).
Proof. exact (MK_COMB (@lem3694950 B) (@lem3694949 B)). Qed.
Lemma lem3694952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3694953 {B : Type'} : (term28 B) = (term28 B).
Proof. exact (MK_COMB (@lem3694952) (@lem3694951 B)). Qed.
Lemma lem3694954 {A B : Type'} : (term30 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3694953 B) (@lem3694937 A B)). Qed.
Lemma lem3694959 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) (t : B -> Prop) : (term73 _87604 B s f t) = (term73 _87604 B s f t).
Proof. exact (eq_refl (term73 _87604 B s f t)). Qed.
Lemma lem3694960 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) : (term74 _87604 B s f) = (term74 _87604 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3694959 _87604 B s f t)). Qed.
Lemma lem3694961 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3694962 {_87604 B : Type'} (s : B -> Prop) (f : B -> _87604) : (term75 _87604 B s f) = (term75 _87604 B s f).
Proof. exact (MK_COMB (@lem3694961 B) (@lem3694960 _87604 B s f)). Qed.
Lemma lem3694963 {_87604 B : Type'} (f : B -> _87604) : (term76 _87604 B f) = (term76 _87604 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3694962 _87604 B s f)). Qed.
Lemma lem3694964 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3694965 {_87604 B : Type'} (f : B -> _87604) : (term77 _87604 B f) = (term77 _87604 B f).
Proof. exact (MK_COMB (@lem3694964 B) (@lem3694963 _87604 B f)). Qed.
Lemma lem3694966 {_87604 B : Type'} : (term78 _87604 B) = (term78 _87604 B).
Proof. exact (fun_ext (fun f : B -> _87604 => @lem3694965 _87604 B f)). Qed.
Lemma lem3694967 {_87604 B : Type'} : (@all (B -> _87604)) = (@all (B -> _87604)).
Proof. exact (eq_refl (@all (B -> _87604))). Qed.
Lemma lem3694968 {_87604 B : Type'} : (term13 _87604 B) = (term13 _87604 B).
Proof. exact (MK_COMB (@lem3694967 _87604 B) (@lem3694966 _87604 B)). Qed.
Lemma lem3694969 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3694970 {_87604 B : Type'} : (term31 _87604 B) = (term31 _87604 B).
Proof. exact (MK_COMB (@lem3694969) (@lem3694968 _87604 B)). Qed.
Lemma lem3694971 {_87604 A B : Type'} : (term33 _87604 A B) = (term33 _87604 A B).
Proof. exact (MK_COMB (@lem3694970 _87604 B) (@lem3694954 A B)). Qed.
Lemma lem3694976 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term79 A B s f t) = (term79 A B s f t).
Proof. exact (eq_refl (term79 A B s f t)). Qed.
Lemma lem3694977 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term80 A B s f) = (term80 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3694976 A B s f t)). Qed.
Lemma lem3694978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3694979 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term81 A B s f).
Proof. exact (MK_COMB (@lem3694978 A) (@lem3694977 A B s f)). Qed.
Lemma lem3694980 {A B : Type'} (f : A -> B) : (term82 A B f) = (term82 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3694979 A B s f)). Qed.
Lemma lem3694981 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3694982 {A B : Type'} (f : A -> B) : (term83 A B f) = (term83 A B f).
Proof. exact (MK_COMB (@lem3694981 A) (@lem3694980 A B f)). Qed.
Lemma lem3694983 {A B : Type'} : (term84 A B) = (term84 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3694982 A B f)). Qed.
Lemma lem3694984 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3694985 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem3694984 A B) (@lem3694983 A B)). Qed.
Lemma lem3694986 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3694987 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem3694986) (@lem3694985 A B)). Qed.
Lemma lem3694988 {_87604 A B : Type'} : (term36 _87604 A B) = (term36 _87604 A B).
Proof. exact (MK_COMB (@lem3694987 A B) (@lem3694971 _87604 A B)). Qed.
Lemma lem3694993 {A : Type'} (s : A -> Prop) (f : A -> A) (t : A -> Prop) : (term67 A s f t) = (term67 A s f t).
Proof. exact (eq_refl (term67 A s f t)). Qed.
Lemma lem3694994 {A : Type'} (s : A -> Prop) (f : A -> A) : (term68 A s f) = (term68 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3694993 A s f t)). Qed.
Lemma lem3694995 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3694996 {A : Type'} (s : A -> Prop) (f : A -> A) : (term69 A s f) = (term69 A s f).
Proof. exact (MK_COMB (@lem3694995 A) (@lem3694994 A s f)). Qed.
Lemma lem3694997 {A : Type'} (f : A -> A) : (term70 A f) = (term70 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3694996 A s f)). Qed.
Lemma lem3694998 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3694999 {A : Type'} (f : A -> A) : (term71 A f) = (term71 A f).
Proof. exact (MK_COMB (@lem3694998 A) (@lem3694997 A f)). Qed.
Lemma lem3695000 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3694999 A f)). Qed.
Lemma lem3695001 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3695002 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem3695001 A) (@lem3695000 A)). Qed.
Lemma lem3695003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3695004 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3695003) (@lem3695002 A)). Qed.
Lemma lem3695005 {_87604 A B : Type'} : (term38 _87604 A B) = (term38 _87604 A B).
Proof. exact (MK_COMB (@lem3695004 A) (@lem3694988 _87604 A B)). Qed.
Lemma lem3695010 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) (t : A -> Prop) : (term73 _87604 A s f t) = (term73 _87604 A s f t).
Proof. exact (eq_refl (term73 _87604 A s f t)). Qed.
Lemma lem3695011 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) : (term74 _87604 A s f) = (term74 _87604 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3695010 _87604 A s f t)). Qed.
Lemma lem3695012 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3695013 {_87604 A : Type'} (s : A -> Prop) (f : A -> _87604) : (term75 _87604 A s f) = (term75 _87604 A s f).
Proof. exact (MK_COMB (@lem3695012 A) (@lem3695011 _87604 A s f)). Qed.
Lemma lem3695014 {_87604 A : Type'} (f : A -> _87604) : (term76 _87604 A f) = (term76 _87604 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3695013 _87604 A s f)). Qed.
Lemma lem3695015 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3695016 {_87604 A : Type'} (f : A -> _87604) : (term77 _87604 A f) = (term77 _87604 A f).
Proof. exact (MK_COMB (@lem3695015 A) (@lem3695014 _87604 A f)). Qed.
Lemma lem3695017 {_87604 A : Type'} : (term78 _87604 A) = (term78 _87604 A).
Proof. exact (fun_ext (fun f : A -> _87604 => @lem3695016 _87604 A f)). Qed.
Lemma lem3695018 {_87604 A : Type'} : (@all (A -> _87604)) = (@all (A -> _87604)).
Proof. exact (eq_refl (@all (A -> _87604))). Qed.
Lemma lem3695019 {_87604 A : Type'} : (term13 _87604 A) = (term13 _87604 A).
Proof. exact (MK_COMB (@lem3695018 _87604 A) (@lem3695017 _87604 A)). Qed.
Lemma lem3695020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3695021 {_87604 A : Type'} : (term31 _87604 A) = (term31 _87604 A).
Proof. exact (MK_COMB (@lem3695020) (@lem3695019 _87604 A)). Qed.
Lemma lem3695022 {_87604 A B : Type'} : (term40 _87604 A B) = (term40 _87604 A B).
Proof. exact (MK_COMB (@lem3695021 _87604 A) (@lem3695005 _87604 A B)). Qed.
Lemma lem3695027 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) (t : _87593 -> Prop) : (term79 _87593 B s f t) = (term79 _87593 B s f t).
Proof. exact (eq_refl (term79 _87593 B s f t)). Qed.
Lemma lem3695028 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) : (term80 _87593 B s f) = (term80 _87593 B s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3695027 _87593 B s f t)). Qed.
Lemma lem3695029 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3695030 {_87593 B : Type'} (s : _87593 -> Prop) (f : _87593 -> B) : (term81 _87593 B s f) = (term81 _87593 B s f).
Proof. exact (MK_COMB (@lem3695029 _87593) (@lem3695028 _87593 B s f)). Qed.
Lemma lem3695031 {_87593 B : Type'} (f : _87593 -> B) : (term82 _87593 B f) = (term82 _87593 B f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3695030 _87593 B s f)). Qed.
Lemma lem3695032 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3695033 {_87593 B : Type'} (f : _87593 -> B) : (term83 _87593 B f) = (term83 _87593 B f).
Proof. exact (MK_COMB (@lem3695032 _87593) (@lem3695031 _87593 B f)). Qed.
Lemma lem3695034 {_87593 B : Type'} : (term84 _87593 B) = (term84 _87593 B).
Proof. exact (fun_ext (fun f : _87593 -> B => @lem3695033 _87593 B f)). Qed.
Lemma lem3695035 {_87593 B : Type'} : (@all (_87593 -> B)) = (@all (_87593 -> B)).
Proof. exact (eq_refl (@all (_87593 -> B))). Qed.
Lemma lem3695036 {_87593 B : Type'} : (term14 _87593 B) = (term14 _87593 B).
Proof. exact (MK_COMB (@lem3695035 _87593 B) (@lem3695034 _87593 B)). Qed.
Lemma lem3695037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3695038 {_87593 B : Type'} : (term34 _87593 B) = (term34 _87593 B).
Proof. exact (MK_COMB (@lem3695037) (@lem3695036 _87593 B)). Qed.
Lemma lem3695039 {_87593 _87604 A B : Type'} : (term42 _87593 _87604 A B) = (term42 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3695038 _87593 B) (@lem3695022 _87604 A B)). Qed.
Lemma lem3695044 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) (t : _87593 -> Prop) : (term79 _87593 A s f t) = (term79 _87593 A s f t).
Proof. exact (eq_refl (term79 _87593 A s f t)). Qed.
Lemma lem3695045 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) : (term80 _87593 A s f) = (term80 _87593 A s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3695044 _87593 A s f t)). Qed.
Lemma lem3695046 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3695047 {_87593 A : Type'} (s : _87593 -> Prop) (f : _87593 -> A) : (term81 _87593 A s f) = (term81 _87593 A s f).
Proof. exact (MK_COMB (@lem3695046 _87593) (@lem3695045 _87593 A s f)). Qed.
Lemma lem3695048 {_87593 A : Type'} (f : _87593 -> A) : (term82 _87593 A f) = (term82 _87593 A f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3695047 _87593 A s f)). Qed.
Lemma lem3695049 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3695050 {_87593 A : Type'} (f : _87593 -> A) : (term83 _87593 A f) = (term83 _87593 A f).
Proof. exact (MK_COMB (@lem3695049 _87593) (@lem3695048 _87593 A f)). Qed.
Lemma lem3695051 {_87593 A : Type'} : (term84 _87593 A) = (term84 _87593 A).
Proof. exact (fun_ext (fun f : _87593 -> A => @lem3695050 _87593 A f)). Qed.
Lemma lem3695052 {_87593 A : Type'} : (@all (_87593 -> A)) = (@all (_87593 -> A)).
Proof. exact (eq_refl (@all (_87593 -> A))). Qed.
Lemma lem3695053 {_87593 A : Type'} : (term14 _87593 A) = (term14 _87593 A).
Proof. exact (MK_COMB (@lem3695052 _87593 A) (@lem3695051 _87593 A)). Qed.
Lemma lem3695054 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3695055 {_87593 A : Type'} : (term34 _87593 A) = (term34 _87593 A).
Proof. exact (MK_COMB (@lem3695054) (@lem3695053 _87593 A)). Qed.
Lemma lem3695056 {_87593 _87604 A B : Type'} : (term44 _87593 _87604 A B) = (term44 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3695055 _87593 A) (@lem3695039 _87593 _87604 A B)). Qed.
Lemma lem3695061 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term85 A B t f s) = (term85 A B t f s).
Proof. exact (eq_refl (term85 A B t f s)). Qed.
Lemma lem3695070 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term86 A B s t f s') = (term86 A B s t f s').
Proof. exact (eq_refl (term86 A B s t f s')). Qed.
Lemma lem3695071 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term87 A B s t f) = (term87 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3695070 A B s t f s')). Qed.
Lemma lem3695072 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3695073 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term88 A B s t f) = (term88 A B s t f).
Proof. exact (MK_COMB (@lem3695072 A) (@lem3695071 A B s t f)). Qed.
Lemma lem3695074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3695075 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term89 A B s t f) = (term89 A B s t f).
Proof. exact (MK_COMB (@lem3695074) (@lem3695073 A B s t f)). Qed.
Lemma lem3695076 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term8 A B t f s) = (term8 A B t f s).
Proof. exact (MK_COMB (@lem3695075 A B s t f) (@lem3695061 A B t f s)). Qed.
Lemma lem3695077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3695078 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term10 A B t f s) = (term10 A B t f s).
Proof. exact (MK_COMB (@lem3695077) (@lem3695076 A B t f s)). Qed.
Lemma lem3695079 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3695080 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term45 A B t f s) = (term45 A B t f s).
Proof. exact (MK_COMB (@lem3695079) (@lem3695078 A B t f s)). Qed.
Lemma lem3695081 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term46 _87593 _87604 A B t f s) = (term46 _87593 _87604 A B t f s).
Proof. exact (MK_COMB (@lem3695080 A B t f s) (@lem3695056 _87593 _87604 A B)). Qed.
Lemma lem3695082 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 _87593 _87604 A B f s) = (term48 _87593 _87604 A B f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3695081 _87593 _87604 A B t f s)). Qed.
Lemma lem3695083 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3695084 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) : (term50 _87593 _87604 A B f s) = (term50 _87593 _87604 A B f s).
Proof. exact (MK_COMB (@lem3695083 B) (@lem3695082 _87593 _87604 A B f s)). Qed.
Lemma lem3695085 {_87593 _87604 A B : Type'} (s : A -> Prop) : (term52 _87593 _87604 A B s) = (term52 _87593 _87604 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem3695084 _87593 _87604 A B f s)). Qed.
Lemma lem3695086 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3695087 {_87593 _87604 A B : Type'} (s : A -> Prop) : (term54 _87593 _87604 A B s) = (term54 _87593 _87604 A B s).
Proof. exact (MK_COMB (@lem3695086 A B) (@lem3695085 _87593 _87604 A B s)). Qed.
Lemma lem3695088 {_87593 _87604 A B : Type'} : (term56 _87593 _87604 A B) = (term56 _87593 _87604 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3695087 _87593 _87604 A B s)). Qed.
Lemma lem3695089 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3695090 {_87593 _87604 A B : Type'} : (term58 _87593 _87604 A B) = (term58 _87593 _87604 A B).
Proof. exact (MK_COMB (@lem3695089 A) (@lem3695088 _87593 _87604 A B)). Qed.
Lemma lem3695327 {_87593 _87604 A B : Type'} : (term57 _87593 _87604 A B) = (term58 _87593 _87604 A B).
Proof. exact (TRANS (@lem3694896 _87593 _87604 A B) (@lem3695090 _87593 _87604 A B)). Qed.
Lemma lem3695328 {_87593 _87604 A B : Type'} : (term58 _87593 _87604 A B) = (term57 _87593 _87604 A B).
Proof. exact (SYM (@lem3695327 _87593 _87604 A B)). Qed.
Lemma lem3695329 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term10 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3695334 {A B : Type'} (h1 : term14 A B) : term14 A B.
Proof. exact (h1). Qed.
Lemma lem3695338 {A B : Type'} (h1 : term11 A B) : term11 A B.
Proof. exact (h1). Qed.
Lemma lem3695348 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term86 A B s t f s') = (term86 A B s t f s').
Proof. exact (eq_refl (term86 A B s t f s')). Qed.
Lemma lem3695349 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term87 A B s t f) = (term87 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3695348 A B s t f s')). Qed.
Lemma lem3695350 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3695351 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term88 A B s t f) = (term88 A B s t f).
Proof. exact (MK_COMB (@lem3695350 A) (@lem3695349 A B s t f)). Qed.
Lemma lem3695358 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term90 A B t f s) = (term91 A B t f s).
Proof. exact (@lem17045 (@FINITE B t) (term92 A B t f s)). Qed.
Lemma lem3695359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3695360 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term93 A B s t f) = (term93 A B s t f).
Proof. exact (MK_COMB (@lem3695359) (@lem3695351 A B s t f)). Qed.
Lemma lem3695361 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term94 A B t f s) = (term95 A B t f s).
Proof. exact (MK_COMB (@lem3695360 A B s t f) (@lem3695358 A B t f s)). Qed.
Lemma lem3695362 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term10 A B t f s) = (term94 A B t f s).
Proof. exact (@lem17362 (term88 A B s t f) (term85 A B t f s)). Qed.
Lemma lem3695363 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term10 A B t f s) = (term95 A B t f s).
Proof. exact (TRANS (@lem3695362 A B t f s) (@lem3695361 A B t f s)). Qed.
Lemma lem3695394 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3695395 {A : Type'} (P : type686 A) (Q : Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (@lem3695394 (A -> Prop) P Q). Qed.
Lemma lem3695396 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term100 A B t f s) = (term101 A B t f s).
Proof. exact (@lem3695395 A (term87 A B s t f) (term91 A B t f s)). Qed.
Lemma lem3695397 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term102 A B s t f s') = (term86 A B s t f s').
Proof. exact (eq_refl (term102 A B s t f s')). Qed.
Lemma lem3695398 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term103 A B s t f) = (term87 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3695397 A B s t f s')). Qed.
Lemma lem3695399 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3695400 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term104 A B s t f) = (term88 A B s t f).
Proof. exact (MK_COMB (@lem3695399 A) (@lem3695398 A B s t f)). Qed.
Lemma lem3695401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3695402 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term105 A B s t f) = (term93 A B s t f).
Proof. exact (MK_COMB (@lem3695401) (@lem3695400 A B s t f)). Qed.
Lemma lem3695403 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term91 A B t f s) = (term91 A B t f s).
Proof. exact (eq_refl (term91 A B t f s)). Qed.
Lemma lem3695404 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term100 A B t f s) = (term95 A B t f s).
Proof. exact (MK_COMB (@lem3695402 A B s t f) (@lem3695403 A B t f s)). Qed.
Lemma lem3695405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3695406 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term106 A B t f s) = (term107 A B t f s).
Proof. exact (MK_COMB (@lem3695405) (@lem3695404 A B t f s)). Qed.
Lemma lem3695407 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term102 A B s t f s') = (term86 A B s t f s').
Proof. exact (eq_refl (term102 A B s t f s')). Qed.
Lemma lem3695408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3695409 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term108 A B s t f s') = (term109 A B s t f s').
Proof. exact (MK_COMB (@lem3695408) (@lem3695407 A B s t f s')). Qed.
Lemma lem3695410 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term91 A B t f s) = (term91 A B t f s).
Proof. exact (eq_refl (term91 A B t f s)). Qed.
Lemma lem3695411 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term110 A B s' t f s) = (term111 A B s' t f s).
Proof. exact (MK_COMB (@lem3695409 A B s t f s') (@lem3695410 A B t f s)). Qed.
Lemma lem3695412 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term112 A B t f s) = (term113 A B t f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3695411 A B s' t f s)). Qed.
Lemma lem3695413 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3695414 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term101 A B t f s) = (term114 A B t f s).
Proof. exact (MK_COMB (@lem3695413 A) (@lem3695412 A B t f s)). Qed.
Lemma lem3695415 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : ((term100 A B t f s) = (term101 A B t f s)) = ((term95 A B t f s) = (term114 A B t f s)).
Proof. exact (MK_COMB (@lem3695406 A B t f s) (@lem3695414 A B t f s)). Qed.
Lemma lem3695417 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term95 A B t f s) = (term114 A B t f s).
Proof. exact (EQ_MP (@lem3695415 A B t f s) (@lem3695396 A B t f s)). Qed.
Lemma lem3695418 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term10 A B t f s) = (term114 A B t f s).
Proof. exact (TRANS (@lem3695363 A B t f s) (@lem3695417 A B t f s)). Qed.
Lemma lem3695419 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term114 A B t f s.
Proof. exact (EQ_MP (@lem3695418 A B t f s) (@lem3695329 A B t f s h1)). Qed.
Lemma lem3695734 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term79 A B s f t) = (term115 A B s f t).
Proof. exact (@lem17265 (@SUBSET A s t) (term116 A B s f t)). Qed.
Lemma lem3695735 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term80 A B s f) = (term117 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3695734 A B s f t)). Qed.
Lemma lem3695736 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3695737 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem3695736 A) (@lem3695735 A B s f)). Qed.
Lemma lem3695738 {A B : Type'} (f : A -> B) : (term82 A B f) = (term119 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3695737 A B s f)). Qed.
Lemma lem3695739 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3695740 {A B : Type'} (f : A -> B) : (term83 A B f) = (term120 A B f).
Proof. exact (MK_COMB (@lem3695739 A) (@lem3695738 A B f)). Qed.
Lemma lem3695741 {A B : Type'} : (term84 A B) = (term121 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3695740 A B f)). Qed.
Lemma lem3695742 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3695803 {A B : Type'} : (term14 A B) = (term122 A B).
Proof. exact (MK_COMB (@lem3695742 A B) (@lem3695741 A B)). Qed.
Lemma lem3695804 {A B : Type'} (h1 : term14 A B) : term122 A B.
Proof. exact (EQ_MP (@lem3695803 A B) (@lem3695334 A B h1)). Qed.
Lemma lem3696035 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term63 A B f s) = (term123 A B f s).
Proof. exact (@lem17265 (@FINITE A s) (term124 A B f s)). Qed.
Lemma lem3696036 {A B : Type'} (f : A -> B) : (term64 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3696035 A B f s)). Qed.
Lemma lem3696037 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3696038 {A B : Type'} (f : A -> B) : (term65 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem3696037 A) (@lem3696036 A B f)). Qed.
Lemma lem3696039 {A B : Type'} : (term66 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3696038 A B f)). Qed.
Lemma lem3696040 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3696097 {A B : Type'} : (term11 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem3696040 A B) (@lem3696039 A B)). Qed.
Lemma lem3696098 {A B : Type'} (h1 : term11 A B) : term128 A B.
Proof. exact (EQ_MP (@lem3696097 A B) (@lem3695338 A B h1)). Qed.
Lemma lem3696324 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term115 A B s f t) = (term115 A B s f t).
Proof. exact (eq_refl (term115 A B s f t)). Qed.
Lemma lem3696325 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term117 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3696324 A B s f t)). Qed.
Lemma lem3696326 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3696327 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem3696326 A) (@lem3696325 A B s f)). Qed.
Lemma lem3696328 {A B : Type'} (f : A -> B) : (term119 A B f) = (term119 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3696327 A B s f)). Qed.
Lemma lem3696329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3696330 {A B : Type'} (f : A -> B) : (term120 A B f) = (term120 A B f).
Proof. exact (MK_COMB (@lem3696329 A) (@lem3696328 A B f)). Qed.
Lemma lem3696331 {A B : Type'} : (term121 A B) = (term121 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3696330 A B f)). Qed.
Lemma lem3696332 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3696333 {A B : Type'} : (term122 A B) = (term122 A B).
Proof. exact (MK_COMB (@lem3696332 A B) (@lem3696331 A B)). Qed.
Lemma lem3696334 {A B : Type'} (h1 : term14 A B) : term122 A B.
Proof. exact (EQ_MP (@lem3696333 A B) (@lem3695804 A B h1)). Qed.
Lemma lem3696437 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term123 A B f s).
Proof. exact (eq_refl (term123 A B f s)). Qed.
Lemma lem3696438 {A B : Type'} (f : A -> B) : (term125 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3696437 A B f s)). Qed.
Lemma lem3696439 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3696440 {A B : Type'} (f : A -> B) : (term126 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem3696439 A) (@lem3696438 A B f)). Qed.
Lemma lem3696441 {A B : Type'} : (term127 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3696440 A B f)). Qed.
Lemma lem3696442 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3696443 {A B : Type'} : (term128 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem3696442 A B) (@lem3696441 A B)). Qed.
Lemma lem3696444 {A B : Type'} (h1 : term11 A B) : term128 A B.
Proof. exact (EQ_MP (@lem3696443 A B) (@lem3696098 A B h1)). Qed.
Lemma lem3696512 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : term111 A B s' t f s.
Proof. exact (h1). Qed.
Lemma lem3696513 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : term91 A B t f s.
Proof. exact (proj2 (@lem3696512 A B s' t f s h1)). Qed.
Lemma lem3696514 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : term86 A B s t f s'.
Proof. exact (proj1 (@lem3696512 A B s' t f s h1)). Qed.
Lemma lem3696515 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : term129 A B s t f s'.
Proof. exact (proj2 (@lem3696514 A B s' t f s h1)). Qed.
Lemma lem3696677 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term123 A B f s).
Proof. exact (eq_refl (term123 A B f s)). Qed.
Lemma lem3696678 {A B : Type'} (f : A -> B) : (term125 A B f) = (term125 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3696677 A B f s)). Qed.
Lemma lem3696679 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3696680 {A B : Type'} (f : A -> B) : (term126 A B f) = (term126 A B f).
Proof. exact (MK_COMB (@lem3696679 A) (@lem3696678 A B f)). Qed.
Lemma lem3696681 {A B : Type'} : (term127 A B) = (term127 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3696680 A B f)). Qed.
Lemma lem3696682 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3696684 {A B : Type'} : (term128 A B) = (term128 A B).
Proof. exact (MK_COMB (@lem3696682 A B) (@lem3696681 A B)). Qed.
Lemma lem3696685 {A B : Type'} (h1 : term11 A B) : term128 A B.
Proof. exact (EQ_MP (@lem3696684 A B) (@lem3696444 A B h1)). Qed.
Lemma lem3696717 {B : Type'} (t : B -> Prop) (h1 : term130 B t) : term130 B t.
Proof. exact (h1). Qed.
Lemma lem3696801 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term115 A B s f t) = (term115 A B s f t).
Proof. exact (eq_refl (term115 A B s f t)). Qed.
Lemma lem3696802 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term117 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3696801 A B s f t)). Qed.
Lemma lem3696803 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3696804 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term118 A B s f) = (term118 A B s f).
Proof. exact (MK_COMB (@lem3696803 A) (@lem3696802 A B s f)). Qed.
Lemma lem3696805 {A B : Type'} (f : A -> B) : (term119 A B f) = (term119 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3696804 A B s f)). Qed.
Lemma lem3696806 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3696807 {A B : Type'} (f : A -> B) : (term120 A B f) = (term120 A B f).
Proof. exact (MK_COMB (@lem3696806 A) (@lem3696805 A B f)). Qed.
Lemma lem3696808 {A B : Type'} : (term121 A B) = (term121 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3696807 A B f)). Qed.
Lemma lem3696809 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3696811 {A B : Type'} : (term122 A B) = (term122 A B).
Proof. exact (MK_COMB (@lem3696809 A B) (@lem3696808 A B)). Qed.
Lemma lem3696812 {A B : Type'} (h1 : term14 A B) : term122 A B.
Proof. exact (EQ_MP (@lem3696811 A B) (@lem3696334 A B h1)). Qed.
Lemma lem3696914 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term131 A B t f s) : term131 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3696984 {A B : Type'} (_42512 : A -> B) (h1 : term11 A B) : term132 A B _42512.
Proof. exact (@lem3696685 A B h1 _42512). Qed.
Lemma lem3696985 {A B : Type'} (_42512 : A -> B) : (term132 A B _42512) = (term126 A B _42512).
Proof. exact (eq_refl (term132 A B _42512)). Qed.
Lemma lem3696986 {A B : Type'} (_42512 : A -> B) (h1 : term11 A B) : term126 A B _42512.
Proof. exact (EQ_MP (@lem3696985 A B _42512) (@lem3696984 A B _42512 h1)). Qed.
Lemma lem3696987 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) (h1 : term11 A B) : term133 A B _42512 _42513.
Proof. exact (@lem3696986 A B _42512 h1 _42513). Qed.
Lemma lem3696988 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term133 A B _42512 _42513) = (term123 A B _42512 _42513).
Proof. exact (eq_refl (term133 A B _42512 _42513)). Qed.
Lemma lem3697032 {A B : Type'} (_42528 : A -> B) (h1 : term14 A B) : term134 A B _42528.
Proof. exact (@lem3696812 A B h1 _42528). Qed.
Lemma lem3697033 {A B : Type'} (_42528 : A -> B) : (term134 A B _42528) = (term120 A B _42528).
Proof. exact (eq_refl (term134 A B _42528)). Qed.
Lemma lem3697034 {A B : Type'} (_42528 : A -> B) (h1 : term14 A B) : term120 A B _42528.
Proof. exact (EQ_MP (@lem3697033 A B _42528) (@lem3697032 A B _42528 h1)). Qed.
Lemma lem3697035 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (h1 : term14 A B) : term135 A B _42528 _42529.
Proof. exact (@lem3697034 A B _42528 h1 _42529). Qed.
Lemma lem3697036 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) : (term135 A B _42528 _42529) = (term118 A B _42529 _42528).
Proof. exact (eq_refl (term135 A B _42528 _42529)). Qed.
Lemma lem3697037 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (h1 : term14 A B) : term118 A B _42529 _42528.
Proof. exact (EQ_MP (@lem3697036 A B _42529 _42528) (@lem3697035 A B _42528 _42529 h1)). Qed.
Lemma lem3697038 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) (h1 : term14 A B) : term136 A B _42529 _42528 _42530.
Proof. exact (@lem3697037 A B _42529 _42528 h1 _42530). Qed.
Lemma lem3697039 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) : (term136 A B _42529 _42528 _42530) = (term115 A B _42529 _42528 _42530).
Proof. exact (eq_refl (term136 A B _42529 _42528 _42530)). Qed.
Lemma lem3697142 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : t = (@IMAGE A B f s').
Proof. exact (proj2 (@lem3696515 A B s' t f s h1)). Qed.
Lemma lem3697144 {B : Type'} (t : B -> Prop) (h1 : term130 B t) : term130 B t.
Proof. exact (h1). Qed.
Lemma lem3697210 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : t = (@IMAGE A B f s').
Proof. exact (proj2 (@lem3696515 A B s' t f s h1)). Qed.
Lemma lem3697212 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term131 A B t f s) : term131 A B t f s.
Proof. exact (h1). Qed.
Lemma lem3697352 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) (h1 : term11 A B) : term123 A B _42512 _42513.
Proof. exact (EQ_MP (@lem3696988 A B _42512 _42513) (@lem3696987 A B _42512 _42513 h1)). Qed.
Lemma lem3697395 {B : Type'} : (term137 B) = (term137 B).
Proof. exact (eq_refl (term137 B)). Qed.
Lemma lem3697396 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : (term138 B t) = (term139 A B f s').
Proof. exact (MK_COMB (@lem3697395 B) (@lem3697142 A B s' t f s h1)). Qed.
Lemma lem3697397 {A B : Type'} (f : A -> B) (s' : A -> Prop) : (term139 A B f s') = (term140 A B f s').
Proof. exact (eq_refl (term139 A B f s')). Qed.
Lemma lem3697398 {B : Type'} (t : B -> Prop) : (term141 B t) = (term141 B t).
Proof. exact (eq_refl (term141 B t)). Qed.
Lemma lem3697399 {A B : Type'} (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : ((term138 B t) = (term139 A B f s')) = ((term138 B t) = (term140 A B f s')).
Proof. exact (MK_COMB (@lem3697398 B t) (@lem3697397 A B f s')). Qed.
Lemma lem3697400 {B : Type'} (t : B -> Prop) : (term138 B t) = (term130 B t).
Proof. exact (eq_refl (term138 B t)). Qed.
Lemma lem3697401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3697402 {B : Type'} (t : B -> Prop) : (term141 B t) = (term142 B t).
Proof. exact (MK_COMB (@lem3697401) (@lem3697400 B t)). Qed.
Lemma lem3697403 {A B : Type'} (f : A -> B) (s' : A -> Prop) : (term140 A B f s') = (term140 A B f s').
Proof. exact (eq_refl (term140 A B f s')). Qed.
Lemma lem3697404 {A B : Type'} (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : ((term138 B t) = (term140 A B f s')) = ((term130 B t) = (term140 A B f s')).
Proof. exact (MK_COMB (@lem3697402 B t) (@lem3697403 A B f s')). Qed.
Lemma lem3697405 {A B : Type'} (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : ((term138 B t) = (term139 A B f s')) = ((term130 B t) = (term140 A B f s')).
Proof. exact (TRANS (@lem3697399 A B t f s') (@lem3697404 A B t f s')). Qed.
Lemma lem3697406 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : (term130 B t) = (term140 A B f s').
Proof. exact (EQ_MP (@lem3697405 A B t f s') (@lem3697396 A B s' t f s h1)). Qed.
Lemma lem3697407 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term130 B t) (h2 : term111 A B s' t f s) : term140 A B f s'.
Proof. exact (EQ_MP (@lem3697406 A B s' t f s h2) (@lem3697144 B t h1)). Qed.
Lemma lem3697491 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) (h1 : term14 A B) : term115 A B _42529 _42528 _42530.
Proof. exact (EQ_MP (@lem3697039 A B _42529 _42528 _42530) (@lem3697038 A B _42529 _42528 _42530 h1)). Qed.
Lemma lem3697590 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term143 A B f s) = (term143 A B f s).
Proof. exact (eq_refl (term143 A B f s)). Qed.
Lemma lem3697591 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : (term144 A B f s t) = (term145 A B s f s').
Proof. exact (MK_COMB (@lem3697590 A B f s) (@lem3697210 A B s' t f s h1)). Qed.
Lemma lem3697592 {A B : Type'} (s' : A -> Prop) (f : A -> B) (s : A -> Prop) : (term145 A B s f s') = (term146 A B s' f s).
Proof. exact (eq_refl (term145 A B s f s')). Qed.
Lemma lem3697593 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term147 A B f s t) = (term147 A B f s t).
Proof. exact (eq_refl (term147 A B f s t)). Qed.
Lemma lem3697594 {A B : Type'} (t : B -> Prop) (s' : A -> Prop) (f : A -> B) (s : A -> Prop) : ((term144 A B f s t) = (term145 A B s f s')) = ((term144 A B f s t) = (term146 A B s' f s)).
Proof. exact (MK_COMB (@lem3697593 A B f s t) (@lem3697592 A B s' f s)). Qed.
Lemma lem3697595 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term144 A B f s t) = (term131 A B t f s).
Proof. exact (eq_refl (term144 A B f s t)). Qed.
Lemma lem3697596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3697597 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term147 A B f s t) = (term148 A B t f s).
Proof. exact (MK_COMB (@lem3697596) (@lem3697595 A B t f s)). Qed.
Lemma lem3697598 {A B : Type'} (s' : A -> Prop) (f : A -> B) (s : A -> Prop) : (term146 A B s' f s) = (term146 A B s' f s).
Proof. exact (eq_refl (term146 A B s' f s)). Qed.
Lemma lem3697599 {A B : Type'} (t : B -> Prop) (s' : A -> Prop) (f : A -> B) (s : A -> Prop) : ((term144 A B f s t) = (term146 A B s' f s)) = ((term131 A B t f s) = (term146 A B s' f s)).
Proof. exact (MK_COMB (@lem3697597 A B t f s) (@lem3697598 A B s' f s)). Qed.
Lemma lem3697600 {A B : Type'} (t : B -> Prop) (s' : A -> Prop) (f : A -> B) (s : A -> Prop) : ((term144 A B f s t) = (term145 A B s f s')) = ((term131 A B t f s) = (term146 A B s' f s)).
Proof. exact (TRANS (@lem3697594 A B t s' f s) (@lem3697599 A B t s' f s)). Qed.
Lemma lem3697601 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : (term131 A B t f s) = (term146 A B s' f s).
Proof. exact (EQ_MP (@lem3697600 A B t s' f s) (@lem3697591 A B s' t f s h1)). Qed.
Lemma lem3697602 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term131 A B t f s) (h2 : term111 A B s' t f s) : term146 A B s' f s.
Proof. exact (EQ_MP (@lem3697601 A B s' t f s h2) (@lem3697212 A B t f s h1)). Qed.
Lemma lem3697604 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : @FINITE A s'.
Proof. exact (proj1 (@lem3696514 A B s' t f s h1)). Qed.
Lemma lem3697605 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : term149 A s'.
Proof. exact (fun h0 : term130 A s' => @lem3697604 A B s' t f s h1). Qed.
Lemma lem3697607 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3697608 {A : Type'} (s' : A -> Prop) : (term149 A s') = (@FINITE A s').
Proof. exact (@lem3697607 (@FINITE A s')). Qed.
Lemma lem3697609 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : @FINITE A s'.
Proof. exact (EQ_MP (@lem3697608 A s') (@lem3697605 A B s' t f s h1)). Qed.
Lemma lem3697615 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3697616 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term123 A B _42512 _42513) = (term151 A B _42512 _42513).
Proof. exact (@lem3697615 (term124 A B _42512 _42513) (term130 A _42513)). Qed.
Lemma lem3697622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3697623 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term152 A B _42512 _42513) = (term153 A B _42512 _42513).
Proof. exact (MK_COMB (@lem3697622) (@lem3697616 A B _42512 _42513)). Qed.
Lemma lem3697629 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term151 A B _42512 _42513) = (term151 A B _42512 _42513).
Proof. exact (eq_refl (term151 A B _42512 _42513)). Qed.
Lemma lem3697630 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : ((term123 A B _42512 _42513) = (term151 A B _42512 _42513)) = ((term151 A B _42512 _42513) = (term151 A B _42512 _42513)).
Proof. exact (MK_COMB (@lem3697623 A B _42512 _42513) (@lem3697629 A B _42512 _42513)). Qed.
Lemma lem3697632 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3697633 (x : Prop) : (x = x) = True.
Proof. exact (@lem3697632 Prop x). Qed.
Lemma lem3697634 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : ((term151 A B _42512 _42513) = (term151 A B _42512 _42513)) = True.
Proof. exact (@lem3697633 (term151 A B _42512 _42513)). Qed.
Lemma lem3697635 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : ((term123 A B _42512 _42513) = (term151 A B _42512 _42513)) = True.
Proof. exact (TRANS (@lem3697630 A B _42512 _42513) (@lem3697634 A B _42512 _42513)). Qed.
Lemma lem3697636 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : True = ((term123 A B _42512 _42513) = (term151 A B _42512 _42513)).
Proof. exact (SYM (@lem3697635 A B _42512 _42513)). Qed.
Lemma lem3697637 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term123 A B _42512 _42513) = (term151 A B _42512 _42513).
Proof. exact (EQ_MP (@lem3697636 A B _42512 _42513) (@lem0)). Qed.
Lemma lem3697638 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) (h1 : term11 A B) : term151 A B _42512 _42513.
Proof. exact (EQ_MP (@lem3697637 A B _42512 _42513) (@lem3697352 A B _42512 _42513 h1)). Qed.
Lemma lem3697640 (b : Prop) (a : Prop) : (a \/ b) = (term154 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3697641 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term151 A B _42512 _42513) = (term155 A B _42512 _42513).
Proof. exact (@lem3697640 (term130 A _42513) (term124 A B _42512 _42513)). Qed.
Lemma lem3697643 (a : Prop) : (term156 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3697644 {A : Type'} (_42513 : A -> Prop) : (term157 A _42513) = (@FINITE A _42513).
Proof. exact (@lem3697643 (@FINITE A _42513)). Qed.
Lemma lem3697645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3697646 {A : Type'} (_42513 : A -> Prop) : (term158 A _42513) = (term159 A _42513).
Proof. exact (MK_COMB (@lem3697645) (@lem3697644 A _42513)). Qed.
Lemma lem3697647 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term124 A B _42512 _42513) = (term124 A B _42512 _42513).
Proof. exact (eq_refl (term124 A B _42512 _42513)). Qed.
Lemma lem3697648 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term155 A B _42512 _42513) = (term63 A B _42512 _42513).
Proof. exact (MK_COMB (@lem3697646 A _42513) (@lem3697647 A B _42512 _42513)). Qed.
Lemma lem3697649 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) : (term151 A B _42512 _42513) = (term63 A B _42512 _42513).
Proof. exact (TRANS (@lem3697641 A B _42512 _42513) (@lem3697648 A B _42512 _42513)). Qed.
Lemma lem3697652 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) (h1 : term11 A B) : term63 A B _42512 _42513.
Proof. exact (EQ_MP (@lem3697649 A B _42512 _42513) (@lem3697638 A B _42512 _42513 h1)). Qed.
Lemma lem3697653 {A B : Type'} (_42512 : A -> B) (_42513 : A -> Prop) (h1 : term11 A B) : term63 A B _42512 _42513.
Proof. exact (@lem3697652 A B _42512 _42513 h1). Qed.
Lemma lem3697654 {A B : Type'} (_42512 : A -> B) (s' : A -> Prop) (h1 : term11 A B) : term63 A B _42512 s'.
Proof. exact (@lem3697653 A B _42512 s' h1). Qed.
Lemma lem3697657 {A B : Type'} (_42512 : A -> B) (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term111 A B s' t f s) : term124 A B _42512 s'.
Proof. exact (@lem3697654 A B _42512 s' h1 (@lem3697609 A B s' t f s h2)). Qed.
Lemma lem3697658 {A B : Type'} (_42512 : A -> B) (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term111 A B s' t f s) : term124 A B _42512 s'.
Proof. exact (@lem3697657 A B _42512 s' t f s h1 h2). Qed.
Lemma lem3697659 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term111 A B s' t f s) : term124 A B f s'.
Proof. exact (@lem3697658 A B f s' t f s h1 h2). Qed.
Lemma lem3697660 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term111 A B s' t f s) : term160 A B f s'.
Proof. exact (fun h0 : term140 A B f s' => @lem3697659 A B s' t f s h1 h2). Qed.
Lemma lem3697662 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3697663 {A B : Type'} (f : A -> B) (s' : A -> Prop) : (term160 A B f s') = (term124 A B f s').
Proof. exact (@lem3697662 (term124 A B f s')). Qed.
Lemma lem3697664 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term111 A B s' t f s) : term124 A B f s'.
Proof. exact (EQ_MP (@lem3697663 A B f s') (@lem3697660 A B s' t f s h1 h2)). Qed.
Lemma lem3697667 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3697669 {A B : Type'} (f : A -> B) (s' : A -> Prop) : (term140 A B f s') = (term161 A B f s').
Proof. exact (@lem3697667 (term124 A B f s')). Qed.
Lemma lem3697672 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term130 B t) (h2 : term111 A B s' t f s) : term161 A B f s'.
Proof. exact (EQ_MP (@lem3697669 A B f s') (@lem3697407 A B s' t f s h1 h2)). Qed.
Lemma lem3697675 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : False.
Proof. exact (@lem3697672 A B s' t f s h2 h3 (@lem3697664 A B s' t f s h1 h3)). Qed.
Lemma lem3697676 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : term162.
Proof. exact (fun h0 : ~ False => @lem3697675 A B s' t f s h1 h2 h3). Qed.
Lemma lem3697678 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3697679 : term162 = False.
Proof. exact (@lem3697678 False). Qed.
Lemma lem3697682 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : @SUBSET A s' s.
Proof. exact (proj1 (@lem3696515 A B s' t f s h1)). Qed.
Lemma lem3697683 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : term163 A s' s.
Proof. exact (fun h0 : term164 A s' s => @lem3697682 A B s' t f s h1). Qed.
Lemma lem3697685 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3697686 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term163 A s' s) = (@SUBSET A s' s).
Proof. exact (@lem3697685 (@SUBSET A s' s)). Qed.
Lemma lem3697687 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term111 A B s' t f s) : @SUBSET A s' s.
Proof. exact (EQ_MP (@lem3697686 A s' s) (@lem3697683 A B s' t f s h1)). Qed.
Lemma lem3697693 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3697694 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : (term115 A B _42529 _42528 _42530) = (term165 A B _42528 _42529 _42530).
Proof. exact (@lem3697693 (term116 A B _42529 _42528 _42530) (term164 A _42529 _42530)). Qed.
Lemma lem3697700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3697701 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : (term166 A B _42529 _42528 _42530) = (term167 A B _42528 _42529 _42530).
Proof. exact (MK_COMB (@lem3697700) (@lem3697694 A B _42528 _42529 _42530)). Qed.
Lemma lem3697707 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : (term165 A B _42528 _42529 _42530) = (term165 A B _42528 _42529 _42530).
Proof. exact (eq_refl (term165 A B _42528 _42529 _42530)). Qed.
Lemma lem3697708 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : ((term115 A B _42529 _42528 _42530) = (term165 A B _42528 _42529 _42530)) = ((term165 A B _42528 _42529 _42530) = (term165 A B _42528 _42529 _42530)).
Proof. exact (MK_COMB (@lem3697701 A B _42528 _42529 _42530) (@lem3697707 A B _42528 _42529 _42530)). Qed.
Lemma lem3697710 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3697711 (x : Prop) : (x = x) = True.
Proof. exact (@lem3697710 Prop x). Qed.
Lemma lem3697712 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : ((term165 A B _42528 _42529 _42530) = (term165 A B _42528 _42529 _42530)) = True.
Proof. exact (@lem3697711 (term165 A B _42528 _42529 _42530)). Qed.
Lemma lem3697713 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : ((term115 A B _42529 _42528 _42530) = (term165 A B _42528 _42529 _42530)) = True.
Proof. exact (TRANS (@lem3697708 A B _42528 _42529 _42530) (@lem3697712 A B _42528 _42529 _42530)). Qed.
Lemma lem3697714 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : True = ((term115 A B _42529 _42528 _42530) = (term165 A B _42528 _42529 _42530)).
Proof. exact (SYM (@lem3697713 A B _42528 _42529 _42530)). Qed.
Lemma lem3697715 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) : (term115 A B _42529 _42528 _42530) = (term165 A B _42528 _42529 _42530).
Proof. exact (EQ_MP (@lem3697714 A B _42528 _42529 _42530) (@lem0)). Qed.
Lemma lem3697716 {A B : Type'} (_42528 : A -> B) (_42529 : A -> Prop) (_42530 : A -> Prop) (h1 : term14 A B) : term165 A B _42528 _42529 _42530.
Proof. exact (EQ_MP (@lem3697715 A B _42528 _42529 _42530) (@lem3697491 A B _42529 _42528 _42530 h1)). Qed.
Lemma lem3697718 (b : Prop) (a : Prop) : (a \/ b) = (term154 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3697719 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) : (term165 A B _42528 _42529 _42530) = (term168 A B _42529 _42528 _42530).
Proof. exact (@lem3697718 (term164 A _42529 _42530) (term116 A B _42529 _42528 _42530)). Qed.
Lemma lem3697721 (a : Prop) : (term156 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3697722 {A : Type'} (_42529 : A -> Prop) (_42530 : A -> Prop) : (term169 A _42529 _42530) = (@SUBSET A _42529 _42530).
Proof. exact (@lem3697721 (@SUBSET A _42529 _42530)). Qed.
Lemma lem3697723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3697724 {A : Type'} (_42529 : A -> Prop) (_42530 : A -> Prop) : (term170 A _42529 _42530) = (term171 A _42529 _42530).
Proof. exact (MK_COMB (@lem3697723) (@lem3697722 A _42529 _42530)). Qed.
Lemma lem3697725 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) : (term116 A B _42529 _42528 _42530) = (term116 A B _42529 _42528 _42530).
Proof. exact (eq_refl (term116 A B _42529 _42528 _42530)). Qed.
Lemma lem3697726 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) : (term168 A B _42529 _42528 _42530) = (term79 A B _42529 _42528 _42530).
Proof. exact (MK_COMB (@lem3697724 A _42529 _42530) (@lem3697725 A B _42529 _42528 _42530)). Qed.
Lemma lem3697727 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) : (term165 A B _42528 _42529 _42530) = (term79 A B _42529 _42528 _42530).
Proof. exact (TRANS (@lem3697719 A B _42529 _42528 _42530) (@lem3697726 A B _42529 _42528 _42530)). Qed.
Lemma lem3697730 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) (h1 : term14 A B) : term79 A B _42529 _42528 _42530.
Proof. exact (EQ_MP (@lem3697727 A B _42529 _42528 _42530) (@lem3697716 A B _42528 _42529 _42530 h1)). Qed.
Lemma lem3697731 {A B : Type'} (_42529 : A -> Prop) (_42528 : A -> B) (_42530 : A -> Prop) (h1 : term14 A B) : term79 A B _42529 _42528 _42530.
Proof. exact (@lem3697730 A B _42529 _42528 _42530 h1). Qed.
Lemma lem3697732 {A B : Type'} (s' : A -> Prop) (_42528 : A -> B) (s : A -> Prop) (h1 : term14 A B) : term79 A B s' _42528 s.
Proof. exact (@lem3697731 A B s' _42528 s h1). Qed.
Lemma lem3697735 {A B : Type'} (_42528 : A -> B) (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term111 A B s' t f s) : term116 A B s' _42528 s.
Proof. exact (@lem3697732 A B s' _42528 s h1 (@lem3697687 A B s' t f s h2)). Qed.
Lemma lem3697736 {A B : Type'} (_42528 : A -> B) (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term111 A B s' t f s) : term116 A B s' _42528 s.
Proof. exact (@lem3697735 A B _42528 s' t f s h1 h2). Qed.
Lemma lem3697737 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term111 A B s' t f s) : term116 A B s' f s.
Proof. exact (@lem3697736 A B f s' t f s h1 h2). Qed.
Lemma lem3697738 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term111 A B s' t f s) : term172 A B s' f s.
Proof. exact (fun h0 : term146 A B s' f s => @lem3697737 A B s' t f s h1 h2). Qed.
Lemma lem3697740 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3697741 {A B : Type'} (s' : A -> Prop) (f : A -> B) (s : A -> Prop) : (term172 A B s' f s) = (term116 A B s' f s).
Proof. exact (@lem3697740 (term116 A B s' f s)). Qed.
Lemma lem3697742 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term111 A B s' t f s) : term116 A B s' f s.
Proof. exact (EQ_MP (@lem3697741 A B s' f s) (@lem3697738 A B s' t f s h1 h2)). Qed.
Lemma lem3697745 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3697747 {A B : Type'} (s' : A -> Prop) (f : A -> B) (s : A -> Prop) : (term146 A B s' f s) = (term173 A B s' f s).
Proof. exact (@lem3697745 (term116 A B s' f s)). Qed.
Lemma lem3697750 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term131 A B t f s) (h2 : term111 A B s' t f s) : term173 A B s' f s.
Proof. exact (EQ_MP (@lem3697747 A B s' f s) (@lem3697602 A B s' t f s h1 h2)). Qed.
Lemma lem3697753 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : False.
Proof. exact (@lem3697750 A B s' t f s h2 h3 (@lem3697742 A B s' t f s h1 h3)). Qed.
Lemma lem3697754 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : term162.
Proof. exact (fun h0 : ~ False => @lem3697753 A B s' t f s h1 h2 h3). Qed.
Lemma lem3697756 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3697757 : term162 = False.
Proof. exact (@lem3697756 False). Qed.
Lemma lem3697759 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697757) (@lem3697754 A B s' t f s h1 h2 h3)). Qed.
Lemma lem3697760 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697679) (@lem3697676 A B s' t f s h1 h2 h3)). Qed.
Lemma lem3697761 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : (term131 A B t f s) = False.
Proof. exact (prop_ext (fun h4 : term131 A B t f s => @lem3697759 A B s' t f s h1 h2 h3) (fun h4 : False => @lem3697212 A B t f s h2)). Qed.
Lemma lem3697762 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697761 A B s' t f s h1 h2 h3) (@lem3697212 A B t f s h2)). Qed.
Lemma lem3697763 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : (term130 B t) = False.
Proof. exact (prop_ext (fun h4 : term130 B t => @lem3697760 A B s' t f s h1 h2 h3) (fun h4 : False => @lem3697144 B t h2)). Qed.
Lemma lem3697764 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697763 A B s' t f s h1 h2 h3) (@lem3697144 B t h2)). Qed.
Lemma lem3697765 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : (term131 A B t f s) = False.
Proof. exact (prop_ext (fun h4 : term131 A B t f s => @lem3697762 A B s' t f s h1 h2 h3) (fun h4 : False => @lem3696914 A B t f s h2)). Qed.
Lemma lem3697766 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697765 A B s' t f s h1 h2 h3) (@lem3696914 A B t f s h2)). Qed.
Lemma lem3697767 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : (term130 B t) = False.
Proof. exact (prop_ext (fun h4 : term130 B t => @lem3697764 A B s' t f s h1 h2 h3) (fun h4 : False => @lem3696717 B t h2)). Qed.
Lemma lem3697768 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697767 A B s' t f s h1 h2 h3) (@lem3696717 B t h2)). Qed.
Lemma lem3697769 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : (term131 A B t f s) = False.
Proof. exact (prop_ext (fun h4 : term131 A B t f s => @lem3697766 A B s' t f s h1 h2 h3) (fun h4 : False => @lem3696914 A B t f s h2)). Qed.
Lemma lem3697770 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term131 A B t f s) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697769 A B s' t f s h1 h2 h3) (@lem3696914 A B t f s h2)). Qed.
Lemma lem3697771 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : (term130 B t) = False.
Proof. exact (prop_ext (fun h4 : term130 B t => @lem3697768 A B s' t f s h1 h2 h3) (fun h4 : False => @lem3696717 B t h2)). Qed.
Lemma lem3697772 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term11 A B) (h2 : term130 B t) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697771 A B s' t f s h1 h2 h3) (@lem3696717 B t h2)). Qed.
Lemma lem3697773 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term11 A B) (h3 : term111 A B s' t f s) : False.
Proof. exact (or_elim (@lem3696513 A B s' t f s h3) (fun h0 : term130 B t => @lem3697772 A B s' t f s h2 h0 h3) (fun h0 : term131 A B t f s => @lem3697770 A B s' t f s h1 h0 h3)). Qed.
Lemma lem3697774 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term11 A B) (h3 : term111 A B s' t f s) : (term111 A B s' t f s) = False.
Proof. exact (prop_ext (fun h4 : term111 A B s' t f s => @lem3697773 A B s' t f s h1 h2 h3) (fun h4 : False => @lem3696512 A B s' t f s h3)). Qed.
Lemma lem3697775 {A B : Type'} (s' : A -> Prop) (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term11 A B) (h3 : term111 A B s' t f s) : False.
Proof. exact (EQ_MP (@lem3697774 A B s' t f s h1 h2 h3) (@lem3696512 A B s' t f s h3)). Qed.
Lemma lem3697776 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term11 A B) (h3 : term10 A B t f s) : False.
Proof. exact (ex_elim (@lem3695419 A B t f s h3) (fun s' : A -> Prop => fun h0 : term113 A B t f s s' => @lem3697775 A B s' t f s h1 h2 h0)). Qed.
Lemma lem3697777 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term11 A B) (h3 : term10 A B t f s) : term20 B.
Proof. exact (fun h0 : term12 B => @lem3697776 A B t f s h1 h2 h3). Qed.
Lemma lem3697778 {B : Type'} : (term20 B) = (term21 B).
Proof. exact (@lem69 (term12 B)). Qed.
Lemma lem3697779 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term11 A B) (h3 : term10 A B t f s) : term21 B.
Proof. exact (EQ_MP (@lem3697778 B) (@lem3697777 A B t f s h1 h2 h3)). Qed.
Lemma lem3697780 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term10 A B t f s) : term24 A B.
Proof. exact (fun h0 : term11 A B => @lem3697779 A B t f s h1 h0 h2). Qed.
Lemma lem3697781 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term10 A B t f s) : term27 A B.
Proof. exact (fun h0 : term12 A => @lem3697780 A B t f s h1 h2). Qed.
Lemma lem3697782 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term10 A B t f s) : term30 A B.
Proof. exact (fun h0 : term15 B => @lem3697781 A B t f s h1 h2). Qed.
Lemma lem3697783 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term14 A B) (h2 : term10 A B t f s) : term33 _87604 A B.
Proof. exact (fun h0 : term13 _87604 B => @lem3697782 A B t f s h1 h2). Qed.
Lemma lem3697784 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term36 _87604 A B.
Proof. exact (fun h0 : term14 A B => @lem3697783 _87604 A B t f s h0 h1). Qed.
Lemma lem3697785 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term38 _87604 A B.
Proof. exact (fun h0 : term15 A => @lem3697784 _87604 A B t f s h1). Qed.
Lemma lem3697786 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term40 _87604 A B.
Proof. exact (fun h0 : term13 _87604 A => @lem3697785 _87604 A B t f s h1). Qed.
Lemma lem3697787 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term42 _87593 _87604 A B.
Proof. exact (fun h0 : term14 _87593 B => @lem3697786 _87604 A B t f s h1). Qed.
Lemma lem3697788 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term44 _87593 _87604 A B.
Proof. exact (fun h0 : term14 _87593 A => @lem3697787 _87593 _87604 A B t f s h1). Qed.
Lemma lem3697789 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term46 _87593 _87604 A B t f s.
Proof. exact (fun h0 : term10 A B t f s => @lem3697788 _87593 _87604 A B t f s h0). Qed.
Lemma lem3697794 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) : term50 _87593 _87604 A B f s.
Proof. exact (fun t : B -> Prop => @lem3697789 _87593 _87604 A B t f s). Qed.
Lemma lem3697799 {_87593 _87604 A B : Type'} (s : A -> Prop) : term54 _87593 _87604 A B s.
Proof. exact (fun f : A -> B => @lem3697794 _87593 _87604 A B f s). Qed.
Lemma lem3697804 {_87593 _87604 A B : Type'} : term58 _87593 _87604 A B.
Proof. exact (fun s : A -> Prop => @lem3697799 _87593 _87604 A B s). Qed.
Lemma lem3697805 {_87593 _87604 A B : Type'} : term57 _87593 _87604 A B.
Proof. exact (EQ_MP (@lem3695328 _87593 _87604 A B) (@lem3697804 _87593 _87604 A B)). Qed.
Lemma lem3697806 {_87593 _87604 A B : Type'} (s : A -> Prop) : term174 _87593 _87604 A B s.
Proof. exact (@lem3697805 _87593 _87604 A B s). Qed.
Lemma lem3697807 {_87593 _87604 A B : Type'} (s : A -> Prop) : (term174 _87593 _87604 A B s) = (term53 _87593 _87604 A B s).
Proof. exact (eq_refl (term174 _87593 _87604 A B s)). Qed.
Lemma lem3697808 {_87593 _87604 A B : Type'} (s : A -> Prop) : term53 _87593 _87604 A B s.
Proof. exact (EQ_MP (@lem3697807 _87593 _87604 A B s) (@lem3697806 _87593 _87604 A B s)). Qed.
Lemma lem3697809 {_87593 _87604 A B : Type'} (s : A -> Prop) (f : A -> B) : term175 _87593 _87604 A B s f.
Proof. exact (@lem3697808 _87593 _87604 A B s f). Qed.
Lemma lem3697810 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) : (term175 _87593 _87604 A B s f) = (term49 _87593 _87604 A B f s).
Proof. exact (eq_refl (term175 _87593 _87604 A B s f)). Qed.
Lemma lem3697811 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) : term49 _87593 _87604 A B f s.
Proof. exact (EQ_MP (@lem3697810 _87593 _87604 A B f s) (@lem3697809 _87593 _87604 A B s f)). Qed.
Lemma lem3697812 {_87593 _87604 A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term176 _87593 _87604 A B f s t.
Proof. exact (@lem3697811 _87593 _87604 A B f s t). Qed.
Lemma lem3697813 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term176 _87593 _87604 A B f s t) = (term16 _87593 _87604 A B t f s).
Proof. exact (eq_refl (term176 _87593 _87604 A B f s t)). Qed.
Lemma lem3697814 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term16 _87593 _87604 A B t f s.
Proof. exact (EQ_MP (@lem3697813 _87593 _87604 A B t f s) (@lem3697812 _87593 _87604 A B f s t)). Qed.
Lemma lem3697816 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term16 _87593 _87604 A B t f s.
Proof. exact (@lem3694632 _87593 _87604 A B t f s (@lem3697814 _87593 _87604 A B t f s)). Qed.
Lemma lem3697817 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term43 _87593 _87604 A B.
Proof. exact (@lem3697816 _87593 _87604 A B t f s (@lem3694604 A B t f s h1)). Qed.
Lemma lem3697818 {_87593 _87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term41 _87593 _87604 A B.
Proof. exact (@lem3697817 _87593 _87604 A B t f s h1 (@lem3694612 _87593 A)). Qed.
Lemma lem3697819 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term39 _87604 A B.
Proof. exact (@lem3697818 Prop _87604 A B t f s h1 (@lem3694613 Prop B)). Qed.
Lemma lem3697820 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term37 _87604 A B.
Proof. exact (@lem3697819 _87604 A B t f s h1 (@lem3694610 _87604 A)). Qed.
Lemma lem3697821 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term35 _87604 A B.
Proof. exact (@lem3697820 _87604 A B t f s h1 (@lem3694616 A)). Qed.
Lemma lem3697822 {_87604 A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term32 _87604 A B.
Proof. exact (@lem3697821 _87604 A B t f s h1 (@lem3694614 A B)). Qed.
Lemma lem3697823 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term29 A B.
Proof. exact (@lem3697822 Prop A B t f s h1 (@lem3694611 Prop B)). Qed.
Lemma lem3697824 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term26 A B.
Proof. exact (@lem3697823 A B t f s h1 (@lem3694615 B)). Qed.
Lemma lem3697825 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term23 A B.
Proof. exact (@lem3697824 A B t f s h1 (@lem3694607 A)). Qed.
Lemma lem3697826 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : term20 B.
Proof. exact (@lem3697825 A B t f s h1 (@lem3694605 A B)). Qed.
Lemma lem3697827 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : False.
Proof. exact (@lem3697826 A B t f s h1 (@lem3694606 B)). Qed.
Lemma lem3697828 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : (term10 A B t f s) = False.
Proof. exact (prop_ext (fun h2 : term10 A B t f s => @lem3697827 A B t f s h1) (fun h2 : False => @lem3694604 A B t f s h1)). Qed.
Lemma lem3697829 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term10 A B t f s) : False.
Proof. exact (EQ_MP (@lem3697828 A B t f s h1) (@lem3694604 A B t f s h1)). Qed.
Lemma lem3697830 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term9 A B t f s.
Proof. exact (fun h0 : term10 A B t f s => @lem3697829 A B t f s h0). Qed.
Lemma lem3697831 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term8 A B t f s.
Proof. exact (EQ_MP (@lem3694603 A B t f s) (@lem3697830 A B t f s)). Qed.
Lemma lem3697833 {_93870 _93890 : Type'} (s : _93870 -> Prop) (P : type686 _93890) (f : _93870 -> _93890) : (term5 _93870 _93890 f s P) = (term6 _93870 _93890 s P f).
Proof. exact (EQ_MP (@lem3694588 _93870 _93890 s P f) (@lem3694587 _93870 _93890 P f s)). Qed.
Lemma lem3697834 {A B : Type'} (s : A -> Prop) (P : type686 B) (f : A -> B) : (term5 A B f s P) = (term6 A B s P f).
Proof. exact (@lem3697833 A B s P f). Qed.
Lemma lem3697835 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term177 A B s f) = (term178 A B s f).
Proof. exact (@lem3697834 A B s (term179 A B s f) f). Qed.
Lemma lem3697836 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term180 A B s f t) = (term88 A B s t f).
Proof. exact (eq_refl (term180 A B s f t)). Qed.
Lemma lem3697837 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term181 A B t f s) = (term181 A B t f s).
Proof. exact (eq_refl (term181 A B t f s)). Qed.
Lemma lem3697838 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term182 A B s f t) = (term183 A B s t f).
Proof. exact (MK_COMB (@lem3697837 A B t f s) (@lem3697836 A B s t f)). Qed.
Lemma lem3697839 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term184 A B s f) = (term185 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3697838 A B s t f)). Qed.
Lemma lem3697840 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3697841 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term177 A B s f) = (term186 A B s f).
Proof. exact (MK_COMB (@lem3697840 B) (@lem3697839 A B s f)). Qed.
Lemma lem3697842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3697843 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term187 A B s f) = (term188 A B s f).
Proof. exact (MK_COMB (@lem3697842) (@lem3697841 A B s f)). Qed.
Lemma lem3697844 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term189 A B s f t) = (term190 A B s t f).
Proof. exact (eq_refl (term189 A B s f t)). Qed.
Lemma lem3697845 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term191 A t s) = (term191 A t s).
Proof. exact (eq_refl (term191 A t s)). Qed.
Lemma lem3697846 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term192 A B s f t) = (term193 A B s t f).
Proof. exact (MK_COMB (@lem3697845 A t s) (@lem3697844 A B s t f)). Qed.
Lemma lem3697847 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term194 A B s f) = (term195 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3697846 A B s t f)). Qed.
Lemma lem3697848 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3697849 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term178 A B s f) = (term196 A B s f).
Proof. exact (MK_COMB (@lem3697848 A) (@lem3697847 A B s f)). Qed.
Lemma lem3697850 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term177 A B s f) = (term178 A B s f)) = ((term186 A B s f) = (term196 A B s f)).
Proof. exact (MK_COMB (@lem3697843 A B s f) (@lem3697849 A B s f)). Qed.
Lemma lem3697851 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term186 A B s f) = (term196 A B s f).
Proof. exact (EQ_MP (@lem3697850 A B s f) (@lem3697835 A B s f)). Qed.
Lemma lem3697870 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term196 A B s f) = (term186 A B s f).
Proof. exact (SYM (@lem3697851 A B s f)). Qed.
Lemma lem3697872 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3697873 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term196 A B s f) = (term197 A B s f).
Proof. exact (@lem3697872 (term196 A B s f)). Qed.
Lemma lem3697874 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term197 A B s f) = (term196 A B s f).
Proof. exact (SYM (@lem3697873 A B s f)). Qed.
Lemma lem3697875 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term198 A B s f) : term198 A B s f.
Proof. exact (h1). Qed.
Lemma lem3697878 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term197 A B s f) : term197 A B s f.
Proof. exact (h1). Qed.
Lemma lem3697879 {A B : Type'} (s : A -> Prop) (f : A -> B) : term199 A B s f.
Proof. exact (fun h0 : term197 A B s f => @lem3697878 A B s f h0). Qed.
Lemma lem3697880 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term199 A B s f) : term199 A B s f.
Proof. exact (h1). Qed.
Lemma lem3697881 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term197 A B s f) : term197 A B s f.
Proof. exact (h1). Qed.
Lemma lem3697882 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term197 A B s f) (h2 : term199 A B s f) : term197 A B s f.
Proof. exact (@lem3697880 A B s f h2 (@lem3697881 A B s f h1)). Qed.
Lemma lem3697883 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term197 A B s f) : term200 A B s f.
Proof. exact (fun h0 : term199 A B s f => @lem3697882 A B s f h1 h0). Qed.
Lemma lem3697884 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term199 A B s f) : term199 A B s f.
Proof. exact (h1). Qed.
Lemma lem3697885 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term197 A B s f) (h2 : term199 A B s f) : term197 A B s f.
Proof. exact (@lem3697883 A B s f h1 (@lem3697884 A B s f h2)). Qed.
Lemma lem3697886 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term199 A B s f) : term199 A B s f.
Proof. exact (fun h0 : term197 A B s f => @lem3697885 A B s f h0 h1). Qed.
Lemma lem3697887 {A B : Type'} (s : A -> Prop) (f : A -> B) : term201 A B s f.
Proof. exact (fun h0 : term199 A B s f => @lem3697886 A B s f h0). Qed.
Lemma lem3697890 {A B : Type'} (s : A -> Prop) (f : A -> B) : term199 A B s f.
Proof. exact (@lem3697887 A B s f (@lem3697879 A B s f)). Qed.
Lemma lem3697891 {A B : Type'} (s : A -> Prop) (f : A -> B) : term199 A B s f.
Proof. exact (@lem3697890 A B s f). Qed.
Lemma lem3697901 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3697902 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term197 A B s f) = (term202 A B s f).
Proof. exact (@lem3697901 (term198 A B s f)). Qed.
Lemma lem3697904 (t : Prop) : (term156 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3697905 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term202 A B s f) = (term196 A B s f).
Proof. exact (@lem3697904 (term196 A B s f)). Qed.
Lemma lem3697910 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term197 A B s f) = (term196 A B s f).
Proof. exact (TRANS (@lem3697902 A B s f) (@lem3697905 A B s f)). Qed.
Lemma lem3697947 {A B : Type'} (f : A -> B) : (term203 A B f) = (term204 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3697910 A B s f)). Qed.
Lemma lem3697948 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3697949 {A B : Type'} (f : A -> B) : (term205 A B f) = (term206 A B f).
Proof. exact (MK_COMB (@lem3697948 A) (@lem3697947 A B f)). Qed.
Lemma lem3697954 {A B : Type'} : (term207 A B) = (term208 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3697949 A B f)). Qed.
Lemma lem3697955 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3697964 {A B : Type'} : (term209 A B) = (term210 A B).
Proof. exact (MK_COMB (@lem3697955 A B) (@lem3697954 A B)). Qed.
Lemma lem3697973 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term211 A B s t f s') = (term211 A B s t f s').
Proof. exact (eq_refl (term211 A B s t f s')). Qed.
Lemma lem3697974 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term212 A B s t f) = (term212 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3697973 A B s t f s')). Qed.
Lemma lem3697975 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3697976 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term190 A B s t f) = (term190 A B s t f).
Proof. exact (MK_COMB (@lem3697975 A) (@lem3697974 A B s t f)). Qed.
Lemma lem3697983 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term191 A t s) = (term191 A t s).
Proof. exact (eq_refl (term191 A t s)). Qed.
Lemma lem3697984 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term193 A B s t f) = (term193 A B s t f).
Proof. exact (MK_COMB (@lem3697983 A t s) (@lem3697976 A B s t f)). Qed.
Lemma lem3697985 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term195 A B s f) = (term195 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3697984 A B s t f)). Qed.
Lemma lem3697986 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3697987 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term196 A B s f) = (term196 A B s f).
Proof. exact (MK_COMB (@lem3697986 A) (@lem3697985 A B s f)). Qed.
Lemma lem3697988 {A B : Type'} (f : A -> B) : (term204 A B f) = (term204 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3697987 A B s f)). Qed.
Lemma lem3697989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3697990 {A B : Type'} (f : A -> B) : (term206 A B f) = (term206 A B f).
Proof. exact (MK_COMB (@lem3697989 A) (@lem3697988 A B f)). Qed.
Lemma lem3697991 {A B : Type'} : (term208 A B) = (term208 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3697990 A B f)). Qed.
Lemma lem3697992 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3697993 {A B : Type'} : (term210 A B) = (term210 A B).
Proof. exact (MK_COMB (@lem3697992 A B) (@lem3697991 A B)). Qed.
Lemma lem3698028 {A B : Type'} : (term209 A B) = (term210 A B).
Proof. exact (TRANS (@lem3697964 A B) (@lem3697993 A B)). Qed.
Lemma lem3698029 {A B : Type'} : (term210 A B) = (term209 A B).
Proof. exact (SYM (@lem3698028 A B)). Qed.
Lemma lem3698032 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3698033 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term190 A B s t f) = (term213 A B s t f).
Proof. exact (@lem3698032 (term190 A B s t f)). Qed.
Lemma lem3698034 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term213 A B s t f) = (term190 A B s t f).
Proof. exact (SYM (@lem3698033 A B s t f)). Qed.
Lemma lem3698035 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term214 A B s t f.
Proof. exact (h1). Qed.
Lemma lem3698045 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term215 A t s.
Proof. exact (h1). Qed.
Lemma lem3698053 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term216 A B s t f s') = (term217 A B s t f s').
Proof. exact (@lem17045 (@SUBSET A s' s) ((@IMAGE A B f t) = (@IMAGE A B f s'))). Qed.
Lemma lem3698055 {A : Type'} (s' : A -> Prop) : (term218 A s') = (term218 A s').
Proof. exact (eq_refl (term218 A s')). Qed.
Lemma lem3698056 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term219 A B s t f s') = (term220 A B s t f s').
Proof. exact (MK_COMB (@lem3698055 A s') (@lem3698053 A B s t f s')). Qed.
Lemma lem3698057 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term221 A B s t f s') = (term219 A B s t f s').
Proof. exact (@lem17045 (@FINITE A s') (term222 A B s t f s')). Qed.
Lemma lem3698058 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term221 A B s t f s') = (term220 A B s t f s').
Proof. exact (TRANS (@lem3698057 A B s t f s') (@lem3698056 A B s t f s')). Qed.
Lemma lem3698059 {A : Type'} (P : type686 A) : (term223 A P) = (term224 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3698060 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term214 A B s t f) = (term225 A B s t f).
Proof. exact (@lem3698059 A (term212 A B s t f)). Qed.
Lemma lem3698061 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term226 A B s t f s') = (term211 A B s t f s').
Proof. exact (eq_refl (term226 A B s t f s')). Qed.
Lemma lem3698062 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3698063 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term227 A B s t f s') = (term221 A B s t f s').
Proof. exact (MK_COMB (@lem3698062) (@lem3698061 A B s t f s')). Qed.
Lemma lem3698064 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term227 A B s t f s') = (term220 A B s t f s').
Proof. exact (TRANS (@lem3698063 A B s t f s') (@lem3698058 A B s t f s')). Qed.
Lemma lem3698065 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term228 A B s t f) = (term229 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3698064 A B s t f s')). Qed.
Lemma lem3698066 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698067 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term225 A B s t f) = (term230 A B s t f).
Proof. exact (MK_COMB (@lem3698066 A) (@lem3698065 A B s t f)). Qed.
Lemma lem3698120 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term214 A B s t f) = (term230 A B s t f).
Proof. exact (TRANS (@lem3698060 A B s t f) (@lem3698067 A B s t f)). Qed.
Lemma lem3698121 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term230 A B s t f.
Proof. exact (EQ_MP (@lem3698120 A B s t f) (@lem3698035 A B s t f h1)). Qed.
Lemma lem3698133 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term215 A t s.
Proof. exact (h1). Qed.
Lemma lem3698166 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term220 A B s t f s') = (term220 A B s t f s').
Proof. exact (eq_refl (term220 A B s t f s')). Qed.
Lemma lem3698167 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term229 A B s t f) = (term229 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3698166 A B s t f s')). Qed.
Lemma lem3698168 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698169 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term230 A B s t f) = (term230 A B s t f).
Proof. exact (MK_COMB (@lem3698168 A) (@lem3698167 A B s t f)). Qed.
Lemma lem3698170 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term230 A B s t f.
Proof. exact (EQ_MP (@lem3698169 A B s t f) (@lem3698121 A B s t f h1)). Qed.
Lemma lem3698186 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (s' : A -> Prop) : (term220 A B s t f s') = (term220 A B s t f s').
Proof. exact (eq_refl (term220 A B s t f s')). Qed.
Lemma lem3698187 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term229 A B s t f) = (term229 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3698186 A B s t f s')). Qed.
Lemma lem3698188 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698190 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term230 A B s t f) = (term230 A B s t f).
Proof. exact (MK_COMB (@lem3698188 A) (@lem3698187 A B s t f)). Qed.
Lemma lem3698191 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term230 A B s t f.
Proof. exact (EQ_MP (@lem3698190 A B s t f) (@lem3698170 A B s t f h1)). Qed.
Lemma lem3698200 {A B : Type'} (_42599 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term231 A B s t f _42599.
Proof. exact (@lem3698191 A B s t f h1 _42599). Qed.
Lemma lem3698201 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_42599 : A -> Prop) : (term231 A B s t f _42599) = (term220 A B s t f _42599).
Proof. exact (eq_refl (term231 A B s t f _42599)). Qed.
Lemma lem3698212 {A B : Type'} (_42599 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term220 A B s t f _42599.
Proof. exact (EQ_MP (@lem3698201 A B s t f _42599) (@lem3698200 A B _42599 s t f h1)). Qed.
Lemma lem3698270 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : @FINITE A t.
Proof. exact (proj1 (@lem3698133 A t s h1)). Qed.
Lemma lem3698271 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term149 A t.
Proof. exact (fun h0 : term130 A t => @lem3698270 A t s h1). Qed.
Lemma lem3698273 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3698274 {A : Type'} (t : A -> Prop) : (term149 A t) = (@FINITE A t).
Proof. exact (@lem3698273 (@FINITE A t)). Qed.
Lemma lem3698275 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : @FINITE A t.
Proof. exact (EQ_MP (@lem3698274 A t) (@lem3698271 A t s h1)). Qed.
Lemma lem3698277 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : @SUBSET A t s.
Proof. exact (proj2 (@lem3698133 A t s h1)). Qed.
Lemma lem3698278 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term163 A t s.
Proof. exact (fun h0 : term164 A t s => @lem3698277 A t s h1). Qed.
Lemma lem3698280 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3698281 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term163 A t s) = (@SUBSET A t s).
Proof. exact (@lem3698280 (@SUBSET A t s)). Qed.
Lemma lem3698282 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : @SUBSET A t s.
Proof. exact (EQ_MP (@lem3698281 A t s) (@lem3698278 A t s h1)). Qed.
Lemma lem3698284 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem21386 (B -> Prop) x). Qed.
Lemma lem3698285 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem3698284 B x). Qed.
Lemma lem3698286 {A B : Type'} (f : A -> B) (t : A -> Prop) : (@IMAGE A B f t) = (@IMAGE A B f t).
Proof. exact (@lem3698285 B (@IMAGE A B f t)). Qed.
Lemma lem3698287 {A B : Type'} (f : A -> B) (t : A -> Prop) : term232 A B f t.
Proof. exact (fun h0 : term233 A B f t => @lem3698286 A B f t). Qed.
Lemma lem3698289 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3698290 {A B : Type'} (f : A -> B) (t : A -> Prop) : (term232 A B f t) = ((@IMAGE A B f t) = (@IMAGE A B f t)).
Proof. exact (@lem3698289 ((@IMAGE A B f t) = (@IMAGE A B f t))). Qed.
Lemma lem3698291 {A B : Type'} (f : A -> B) (t : A -> Prop) : (@IMAGE A B f t) = (@IMAGE A B f t).
Proof. exact (EQ_MP (@lem3698290 A B f t) (@lem3698287 A B f t)). Qed.
Lemma lem3698293 (a : Prop) (b : Prop) : (term234 a b) = (term235 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3698294 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_42599 : A -> Prop) : (term217 A B s t f _42599) = (term216 A B s t f _42599).
Proof. exact (@lem3698293 (@SUBSET A _42599 s) ((@IMAGE A B f t) = (@IMAGE A B f _42599))). Qed.
Lemma lem3698295 {A : Type'} (_42599 : A -> Prop) : (term218 A _42599) = (term218 A _42599).
Proof. exact (eq_refl (term218 A _42599)). Qed.
Lemma lem3698296 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_42599 : A -> Prop) : (term220 A B s t f _42599) = (term219 A B s t f _42599).
Proof. exact (MK_COMB (@lem3698295 A _42599) (@lem3698294 A B s t f _42599)). Qed.
Lemma lem3698298 (a : Prop) (b : Prop) : (term234 a b) = (term235 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3698299 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_42599 : A -> Prop) : (term219 A B s t f _42599) = (term221 A B s t f _42599).
Proof. exact (@lem3698298 (@FINITE A _42599) (term222 A B s t f _42599)). Qed.
Lemma lem3698300 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_42599 : A -> Prop) : (term220 A B s t f _42599) = (term221 A B s t f _42599).
Proof. exact (TRANS (@lem3698296 A B s t f _42599) (@lem3698299 A B s t f _42599)). Qed.
Lemma lem3698302 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3698303 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_42599 : A -> Prop) : (term221 A B s t f _42599) = (term236 A B s t f _42599).
Proof. exact (@lem3698302 (term211 A B s t f _42599)). Qed.
Lemma lem3698304 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (_42599 : A -> Prop) : (term220 A B s t f _42599) = (term236 A B s t f _42599).
Proof. exact (TRANS (@lem3698300 A B s t f _42599) (@lem3698303 A B s t f _42599)). Qed.
Lemma lem3698306 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term237 A B s f t.
Proof. exact (conj (@lem3698282 A t s h1) (@lem3698291 A B f t)). Qed.
Lemma lem3698307 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term238 A B s f t.
Proof. exact (conj (@lem3698275 A t s h1) (@lem3698306 A B f t s h1)). Qed.
Lemma lem3698309 {A B : Type'} (_42599 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term236 A B s t f _42599.
Proof. exact (EQ_MP (@lem3698304 A B s t f _42599) (@lem3698212 A B _42599 s t f h1)). Qed.
Lemma lem3698310 {A B : Type'} (_42599 : A -> Prop) (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term236 A B s t f _42599.
Proof. exact (@lem3698309 A B _42599 s t f h1). Qed.
Lemma lem3698311 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (h1 : term214 A B s t f) : term239 A B s f t.
Proof. exact (@lem3698310 A B t s t f h1). Qed.
Lemma lem3698314 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : False.
Proof. exact (@lem3698311 A B s t f h1 (@lem3698307 A B f t s h2)). Qed.
Lemma lem3698315 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : term162.
Proof. exact (fun h0 : ~ False => @lem3698314 A B f t s h1 h2). Qed.
Lemma lem3698317 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3698318 : term162 = False.
Proof. exact (@lem3698317 False). Qed.
Lemma lem3698319 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : False.
Proof. exact (EQ_MP (@lem3698318) (@lem3698315 A B f t s h1 h2)). Qed.
Lemma lem3698320 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : (term215 A t s) = False.
Proof. exact (prop_ext (fun h3 : term215 A t s => @lem3698319 A B f t s h1 h2) (fun h3 : False => @lem3698133 A t s h2)). Qed.
Lemma lem3698321 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : False.
Proof. exact (EQ_MP (@lem3698320 A B f t s h1 h2) (@lem3698133 A t s h2)). Qed.
Lemma lem3698322 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : (term215 A t s) = False.
Proof. exact (prop_ext (fun h3 : term215 A t s => @lem3698321 A B f t s h1 h2) (fun h3 : False => @lem3698045 A t s h2)). Qed.
Lemma lem3698323 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : False.
Proof. exact (EQ_MP (@lem3698322 A B f t s h1 h2) (@lem3698045 A t s h2)). Qed.
Lemma lem3698324 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : (term214 A B s t f) = False.
Proof. exact (prop_ext (fun h3 : term214 A B s t f => @lem3698323 A B f t s h1 h2) (fun h3 : False => @lem3698035 A B s t f h1)). Qed.
Lemma lem3698325 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term214 A B s t f) (h2 : term215 A t s) : False.
Proof. exact (EQ_MP (@lem3698324 A B f t s h1 h2) (@lem3698035 A B s t f h1)). Qed.
Lemma lem3698326 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term213 A B s t f.
Proof. exact (fun h0 : term214 A B s t f => @lem3698325 A B f t s h0 h1). Qed.
Lemma lem3698327 {A B : Type'} (f : A -> B) (t : A -> Prop) (s : A -> Prop) (h1 : term215 A t s) : term190 A B s t f.
Proof. exact (EQ_MP (@lem3698034 A B s t f) (@lem3698326 A B f t s h1)). Qed.
Lemma lem3698328 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) : term193 A B s t f.
Proof. exact (fun h0 : term215 A t s => @lem3698327 A B f t s h0). Qed.
Lemma lem3698333 {A B : Type'} (s : A -> Prop) (f : A -> B) : term196 A B s f.
Proof. exact (fun t : A -> Prop => @lem3698328 A B s t f). Qed.
Lemma lem3698338 {A B : Type'} (f : A -> B) : term206 A B f.
Proof. exact (fun s : A -> Prop => @lem3698333 A B s f). Qed.
Lemma lem3698343 {A B : Type'} : term210 A B.
Proof. exact (fun f : A -> B => @lem3698338 A B f). Qed.
Lemma lem3698344 {A B : Type'} : term209 A B.
Proof. exact (EQ_MP (@lem3698029 A B) (@lem3698343 A B)). Qed.
Lemma lem3698345 {A B : Type'} (f : A -> B) : term240 A B f.
Proof. exact (@lem3698344 A B f). Qed.
Lemma lem3698346 {A B : Type'} (f : A -> B) : (term240 A B f) = (term205 A B f).
Proof. exact (eq_refl (term240 A B f)). Qed.
Lemma lem3698347 {A B : Type'} (f : A -> B) : term205 A B f.
Proof. exact (EQ_MP (@lem3698346 A B f) (@lem3698345 A B f)). Qed.
Lemma lem3698348 {A B : Type'} (f : A -> B) (s : A -> Prop) : term241 A B f s.
Proof. exact (@lem3698347 A B f s). Qed.
Lemma lem3698349 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term241 A B f s) = (term197 A B s f).
Proof. exact (eq_refl (term241 A B f s)). Qed.
Lemma lem3698350 {A B : Type'} (s : A -> Prop) (f : A -> B) : term197 A B s f.
Proof. exact (EQ_MP (@lem3698349 A B s f) (@lem3698348 A B f s)). Qed.
Lemma lem3698352 {A B : Type'} (s : A -> Prop) (f : A -> B) : term197 A B s f.
Proof. exact (@lem3697891 A B s f (@lem3698350 A B s f)). Qed.
Lemma lem3698353 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term198 A B s f) : False.
Proof. exact (@lem3698352 A B s f (@lem3697875 A B s f h1)). Qed.
Lemma lem3698354 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term198 A B s f) : (term198 A B s f) = False.
Proof. exact (prop_ext (fun h2 : term198 A B s f => @lem3698353 A B s f h1) (fun h2 : False => @lem3697875 A B s f h1)). Qed.
Lemma lem3698355 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term198 A B s f) : False.
Proof. exact (EQ_MP (@lem3698354 A B s f h1) (@lem3697875 A B s f h1)). Qed.
Lemma lem3698356 {A B : Type'} (s : A -> Prop) (f : A -> B) : term197 A B s f.
Proof. exact (fun h0 : term198 A B s f => @lem3698355 A B s f h0). Qed.
Lemma lem3698357 {A B : Type'} (s : A -> Prop) (f : A -> B) : term196 A B s f.
Proof. exact (EQ_MP (@lem3697874 A B s f) (@lem3698356 A B s f)). Qed.
Lemma lem3698358 {A B : Type'} (s : A -> Prop) (f : A -> B) : term186 A B s f.
Proof. exact (EQ_MP (@lem3697870 A B s f) (@lem3698357 A B s f)). Qed.
Lemma lem3698359 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : B -> Prop) : term242 A B s f t.
Proof. exact (@lem3698358 A B s f t). Qed.
Lemma lem3698360 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term242 A B s f t) = (term183 A B s t f).
Proof. exact (eq_refl (term242 A B s f t)). Qed.
Lemma lem3698361 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term183 A B s t f.
Proof. exact (EQ_MP (@lem3698360 A B s t f) (@lem3698359 A B s f t)). Qed.
Lemma lem3698362 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : term243 A B t f s.
Proof. exact (conj (@lem3698361 A B s t f) (@lem3697831 A B t f s)). Qed.
Lemma lem3698363 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term243 A B t f s) = ((term85 A B t f s) = (term88 A B s t f)).
Proof. exact (@lem32 (term85 A B t f s) (term88 A B s t f)). Qed.
Lemma lem3698364 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term85 A B t f s) = (term88 A B s t f).
Proof. exact (EQ_MP (@lem3698363 A B s t f) (@lem3698362 A B t f s)). Qed.
Lemma lem3698369 {A B : Type'} (s : A -> Prop) (f : A -> B) : term244 A B s f.
Proof. exact (fun t : B -> Prop => @lem3698364 A B s t f). Qed.
Lemma lem3698374 {A B : Type'} (f : A -> B) : term245 A B f.
Proof. exact (fun s : A -> Prop => @lem3698369 A B s f). Qed.
Lemma lem3698379 {A B : Type'} : term246 A B.
Proof. exact (fun f : A -> B => @lem3698374 A B f). Qed.
