Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_SUBSET_IMAGE_spec.
Require Import SUBSET_REFL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem3703681 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3703682 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3703683 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3703682 t1) (@lem3703681 t1)). Qed.
Lemma lem3703684 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3703683 t1 t2). Qed.
Lemma lem3703685 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3703686 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3703685 t1 t2) (@lem3703684 t1 t2)). Qed.
Lemma lem3703687 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3703686 t1 t2 t3). Qed.
Lemma lem3703688 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3703689 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3703688 t1 t2 t3) (@lem3703687 t1 t2 t3)). Qed.
Lemma lem3703690 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3703689 t1 t2 t3)). Qed.
Lemma lem3703692 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3703693 {A B : Type'} : (term8 A B) = (term9 A B).
Proof. exact (@lem3703692 (term8 A B)). Qed.
Lemma lem3703694 {A B : Type'} : (term9 A B) = (term8 A B).
Proof. exact (SYM (@lem3703693 A B)). Qed.
Lemma lem3703695 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem3703696 {A B : Type'} : term11 A B.
Proof. exact (@lem3698379 A B). Qed.
Lemma lem3703697 {A : Type'} : term12 A.
Proof. exact (@lem3698379 A A). Qed.
Lemma lem3703700 {B : Type'} : term12 B.
Proof. exact (@lem3698379 B B). Qed.
Lemma lem3703704 {B : Type'} : term13 B.
Proof. exact (@lem3615104 B B). Qed.
Lemma lem3703705 {A B : Type'} : term14 A B.
Proof. exact (@lem3615104 A B). Qed.
Lemma lem3703707 {A : Type'} : term13 A.
Proof. exact (@lem3615104 A A). Qed.
Lemma lem3703711 {A : Type'} : term15 A.
Proof. exact (@lem3217397 A). Qed.
Lemma lem3703712 {B : Type'} : term15 B.
Proof. exact (@lem3217397 B). Qed.
Lemma lem3703715 {A B : Type'} (h1 : term16 A B) : term16 A B.
Proof. exact (h1). Qed.
Lemma lem3703716 {A B : Type'} : term17 A B.
Proof. exact (fun h0 : term16 A B => @lem3703715 A B h0). Qed.
Lemma lem3703717 {A B : Type'} (h1 : term17 A B) : term17 A B.
Proof. exact (h1). Qed.
Lemma lem3703718 {A B : Type'} (h1 : term16 A B) : term16 A B.
Proof. exact (h1). Qed.
Lemma lem3703719 {A B : Type'} (h1 : term16 A B) (h2 : term17 A B) : term16 A B.
Proof. exact (@lem3703717 A B h2 (@lem3703718 A B h1)). Qed.
Lemma lem3703720 {A B : Type'} (h1 : term16 A B) : term18 A B.
Proof. exact (fun h0 : term17 A B => @lem3703719 A B h1 h0). Qed.
Lemma lem3703721 {A B : Type'} (h1 : term17 A B) : term17 A B.
Proof. exact (h1). Qed.
Lemma lem3703722 {A B : Type'} (h1 : term16 A B) (h2 : term17 A B) : term16 A B.
Proof. exact (@lem3703720 A B h1 (@lem3703721 A B h2)). Qed.
Lemma lem3703723 {A B : Type'} (h1 : term17 A B) : term17 A B.
Proof. exact (fun h0 : term16 A B => @lem3703722 A B h0 h1). Qed.
Lemma lem3703724 {A B : Type'} : term19 A B.
Proof. exact (fun h0 : term17 A B => @lem3703723 A B h0). Qed.
Lemma lem3703727 {A B : Type'} : term17 A B.
Proof. exact (@lem3703724 A B (@lem3703716 A B)). Qed.
Lemma lem3703728 {A B : Type'} : term17 A B.
Proof. exact (@lem3703727 A B). Qed.
Lemma lem3703916 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3703917 {B : Type'} : (term20 B) = (term21 B).
Proof. exact (@lem3703916 (term12 B)). Qed.
Lemma lem3703964 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem3703965 {A B : Type'} : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem3703964 A B) (@lem3703917 B)). Qed.
Lemma lem3703968 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (eq_refl (term25 A)). Qed.
Lemma lem3703969 {A B : Type'} : (term26 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem3703968 A) (@lem3703965 A B)). Qed.
Lemma lem3703972 {B : Type'} : (term28 B) = (term28 B).
Proof. exact (eq_refl (term28 B)). Qed.
Lemma lem3703973 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3703972 B) (@lem3703969 A B)). Qed.
Lemma lem3703976 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (eq_refl (term31 A B)). Qed.
Lemma lem3703977 {A B : Type'} : (term32 A B) = (term33 A B).
Proof. exact (MK_COMB (@lem3703976 A B) (@lem3703973 A B)). Qed.
Lemma lem3703980 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem3703981 {A B : Type'} : (term34 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem3703980 A) (@lem3703977 A B)). Qed.
Lemma lem3703984 {B : Type'} : (term36 B) = (term36 B).
Proof. exact (eq_refl (term36 B)). Qed.
Lemma lem3703985 {A B : Type'} : (term37 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem3703984 B) (@lem3703981 A B)). Qed.
Lemma lem3703988 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (eq_refl (term36 A)). Qed.
Lemma lem3703989 {A B : Type'} : (term39 A B) = (term40 A B).
Proof. exact (MK_COMB (@lem3703988 A) (@lem3703985 A B)). Qed.
Lemma lem3703992 {A B : Type'} : (term41 A B) = (term41 A B).
Proof. exact (eq_refl (term41 A B)). Qed.
Lemma lem3703999 {A B : Type'} : (term16 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem3703992 A B) (@lem3703989 A B)). Qed.
Lemma lem3704008 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term43 B s t f s') = (term43 B s t f s').
Proof. exact (eq_refl (term43 B s t f s')). Qed.
Lemma lem3704009 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term44 B s t f) = (term44 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3704008 B s t f s')). Qed.
Lemma lem3704010 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3704011 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term45 B s t f) = (term45 B s t f).
Proof. exact (MK_COMB (@lem3704010 B) (@lem3704009 B s t f)). Qed.
Lemma lem3704018 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term46 B t f s) = (term46 B t f s).
Proof. exact (eq_refl (term46 B t f s)). Qed.
Lemma lem3704019 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term47 B t f s) = (term45 B s t f)) = ((term47 B t f s) = (term45 B s t f)).
Proof. exact (MK_COMB (@lem3704018 B t f s) (@lem3704011 B s t f)). Qed.
Lemma lem3704020 {B : Type'} (s : B -> Prop) (f : B -> B) : (term48 B s f) = (term48 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3704019 B s t f)). Qed.
Lemma lem3704021 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3704022 {B : Type'} (s : B -> Prop) (f : B -> B) : (term49 B s f) = (term49 B s f).
Proof. exact (MK_COMB (@lem3704021 B) (@lem3704020 B s f)). Qed.
Lemma lem3704023 {B : Type'} (f : B -> B) : (term50 B f) = (term50 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3704022 B s f)). Qed.
Lemma lem3704024 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3704025 {B : Type'} (f : B -> B) : (term51 B f) = (term51 B f).
Proof. exact (MK_COMB (@lem3704024 B) (@lem3704023 B f)). Qed.
Lemma lem3704026 {B : Type'} : (term52 B) = (term52 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3704025 B f)). Qed.
Lemma lem3704027 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3704028 {B : Type'} : (term12 B) = (term12 B).
Proof. exact (MK_COMB (@lem3704027 B) (@lem3704026 B)). Qed.
Lemma lem3704029 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3704030 {B : Type'} : (term21 B) = (term21 B).
Proof. exact (MK_COMB (@lem3704029) (@lem3704028 B)). Qed.
Lemma lem3704039 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term53 A B s t f s') = (term53 A B s t f s').
Proof. exact (eq_refl (term53 A B s t f s')). Qed.
Lemma lem3704040 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term54 A B s t f) = (term54 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3704039 A B s t f s')). Qed.
Lemma lem3704041 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704042 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term55 A B s t f) = (term55 A B s t f).
Proof. exact (MK_COMB (@lem3704041 A) (@lem3704040 A B s t f)). Qed.
Lemma lem3704049 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term56 A B t f s) = (term56 A B t f s).
Proof. exact (eq_refl (term56 A B t f s)). Qed.
Lemma lem3704050 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term57 A B t f s) = (term55 A B s t f)) = ((term57 A B t f s) = (term55 A B s t f)).
Proof. exact (MK_COMB (@lem3704049 A B t f s) (@lem3704042 A B s t f)). Qed.
Lemma lem3704051 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term58 A B s f) = (term58 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3704050 A B s t f)). Qed.
Lemma lem3704052 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3704053 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term59 A B s f).
Proof. exact (MK_COMB (@lem3704052 B) (@lem3704051 A B s f)). Qed.
Lemma lem3704054 {A B : Type'} (f : A -> B) : (term60 A B f) = (term60 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704053 A B s f)). Qed.
Lemma lem3704055 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704056 {A B : Type'} (f : A -> B) : (term61 A B f) = (term61 A B f).
Proof. exact (MK_COMB (@lem3704055 A) (@lem3704054 A B f)). Qed.
Lemma lem3704057 {A B : Type'} : (term62 A B) = (term62 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704056 A B f)). Qed.
Lemma lem3704058 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3704059 {A B : Type'} : (term11 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem3704058 A B) (@lem3704057 A B)). Qed.
Lemma lem3704060 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704061 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem3704060) (@lem3704059 A B)). Qed.
Lemma lem3704062 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem3704061 A B) (@lem3704030 B)). Qed.
Lemma lem3704071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term43 A s t f s') = (term43 A s t f s').
Proof. exact (eq_refl (term43 A s t f s')). Qed.
Lemma lem3704072 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term44 A s t f) = (term44 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3704071 A s t f s')). Qed.
Lemma lem3704073 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term45 A s t f) = (term45 A s t f).
Proof. exact (MK_COMB (@lem3704073 A) (@lem3704072 A s t f)). Qed.
Lemma lem3704081 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term46 A t f s) = (term46 A t f s).
Proof. exact (eq_refl (term46 A t f s)). Qed.
Lemma lem3704082 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term47 A t f s) = (term45 A s t f)) = ((term47 A t f s) = (term45 A s t f)).
Proof. exact (MK_COMB (@lem3704081 A t f s) (@lem3704074 A s t f)). Qed.
Lemma lem3704083 {A : Type'} (s : A -> Prop) (f : A -> A) : (term48 A s f) = (term48 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704082 A s t f)). Qed.
Lemma lem3704084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704085 {A : Type'} (s : A -> Prop) (f : A -> A) : (term49 A s f) = (term49 A s f).
Proof. exact (MK_COMB (@lem3704084 A) (@lem3704083 A s f)). Qed.
Lemma lem3704086 {A : Type'} (f : A -> A) : (term50 A f) = (term50 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704085 A s f)). Qed.
Lemma lem3704087 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704088 {A : Type'} (f : A -> A) : (term51 A f) = (term51 A f).
Proof. exact (MK_COMB (@lem3704087 A) (@lem3704086 A f)). Qed.
Lemma lem3704089 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3704088 A f)). Qed.
Lemma lem3704090 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3704091 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3704090 A) (@lem3704089 A)). Qed.
Lemma lem3704092 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704093 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem3704092) (@lem3704091 A)). Qed.
Lemma lem3704094 {A B : Type'} : (term27 A B) = (term27 A B).
Proof. exact (MK_COMB (@lem3704093 A) (@lem3704062 A B)). Qed.
Lemma lem3704099 {B : Type'} (f : B -> B) (s : B -> Prop) : (term63 B f s) = (term63 B f s).
Proof. exact (eq_refl (term63 B f s)). Qed.
Lemma lem3704100 {B : Type'} (f : B -> B) : (term64 B f) = (term64 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3704099 B f s)). Qed.
Lemma lem3704101 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3704102 {B : Type'} (f : B -> B) : (term65 B f) = (term65 B f).
Proof. exact (MK_COMB (@lem3704101 B) (@lem3704100 B f)). Qed.
Lemma lem3704103 {B : Type'} : (term66 B) = (term66 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3704102 B f)). Qed.
Lemma lem3704104 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3704105 {B : Type'} : (term13 B) = (term13 B).
Proof. exact (MK_COMB (@lem3704104 B) (@lem3704103 B)). Qed.
Lemma lem3704106 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704107 {B : Type'} : (term28 B) = (term28 B).
Proof. exact (MK_COMB (@lem3704106) (@lem3704105 B)). Qed.
Lemma lem3704108 {A B : Type'} : (term30 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3704107 B) (@lem3704094 A B)). Qed.
Lemma lem3704113 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term67 A B f s) = (term67 A B f s).
Proof. exact (eq_refl (term67 A B f s)). Qed.
Lemma lem3704114 {A B : Type'} (f : A -> B) : (term68 A B f) = (term68 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704113 A B f s)). Qed.
Lemma lem3704115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704116 {A B : Type'} (f : A -> B) : (term69 A B f) = (term69 A B f).
Proof. exact (MK_COMB (@lem3704115 A) (@lem3704114 A B f)). Qed.
Lemma lem3704117 {A B : Type'} : (term70 A B) = (term70 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704116 A B f)). Qed.
Lemma lem3704118 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3704119 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem3704118 A B) (@lem3704117 A B)). Qed.
Lemma lem3704120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704121 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem3704120) (@lem3704119 A B)). Qed.
Lemma lem3704122 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (MK_COMB (@lem3704121 A B) (@lem3704108 A B)). Qed.
Lemma lem3704127 {A : Type'} (f : A -> A) (s : A -> Prop) : (term63 A f s) = (term63 A f s).
Proof. exact (eq_refl (term63 A f s)). Qed.
Lemma lem3704128 {A : Type'} (f : A -> A) : (term64 A f) = (term64 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704127 A f s)). Qed.
Lemma lem3704129 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704130 {A : Type'} (f : A -> A) : (term65 A f) = (term65 A f).
Proof. exact (MK_COMB (@lem3704129 A) (@lem3704128 A f)). Qed.
Lemma lem3704131 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3704130 A f)). Qed.
Lemma lem3704132 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3704133 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem3704132 A) (@lem3704131 A)). Qed.
Lemma lem3704134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704135 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3704134) (@lem3704133 A)). Qed.
Lemma lem3704136 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem3704135 A) (@lem3704122 A B)). Qed.
Lemma lem3704137 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3704138 {B : Type'} : (term71 B) = (term71 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3704137 B s)). Qed.
Lemma lem3704139 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3704140 {B : Type'} : (term15 B) = (term15 B).
Proof. exact (MK_COMB (@lem3704139 B) (@lem3704138 B)). Qed.
Lemma lem3704141 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704142 {B : Type'} : (term36 B) = (term36 B).
Proof. exact (MK_COMB (@lem3704141) (@lem3704140 B)). Qed.
Lemma lem3704143 {A B : Type'} : (term38 A B) = (term38 A B).
Proof. exact (MK_COMB (@lem3704142 B) (@lem3704136 A B)). Qed.
Lemma lem3704144 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = (@SUBSET A s s).
Proof. exact (eq_refl (@SUBSET A s s)). Qed.
Lemma lem3704145 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704144 A s)). Qed.
Lemma lem3704146 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704147 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem3704146 A) (@lem3704145 A)). Qed.
Lemma lem3704148 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704149 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem3704148) (@lem3704147 A)). Qed.
Lemma lem3704150 {A B : Type'} : (term40 A B) = (term40 A B).
Proof. exact (MK_COMB (@lem3704149 A) (@lem3704143 A B)). Qed.
Lemma lem3704159 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term72 A B s f t) = (term72 A B s f t).
Proof. exact (eq_refl (term72 A B s f t)). Qed.
Lemma lem3704160 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term73 A B s f) = (term73 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704159 A B s f t)). Qed.
Lemma lem3704161 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704162 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term74 A B s f) = (term74 A B s f).
Proof. exact (MK_COMB (@lem3704161 A) (@lem3704160 A B s f)). Qed.
Lemma lem3704165 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term75 A B f s) = (term75 A B f s).
Proof. exact (eq_refl (term75 A B f s)). Qed.
Lemma lem3704166 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term76 A B f s) = (term74 A B s f)) = ((term76 A B f s) = (term74 A B s f)).
Proof. exact (MK_COMB (@lem3704165 A B f s) (@lem3704162 A B s f)). Qed.
Lemma lem3704167 {A B : Type'} (f : A -> B) : (term77 A B f) = (term77 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704166 A B s f)). Qed.
Lemma lem3704168 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704169 {A B : Type'} (f : A -> B) : (term78 A B f) = (term78 A B f).
Proof. exact (MK_COMB (@lem3704168 A) (@lem3704167 A B f)). Qed.
Lemma lem3704170 {A B : Type'} : (term79 A B) = (term79 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704169 A B f)). Qed.
Lemma lem3704171 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3704172 {A B : Type'} : (term8 A B) = (term8 A B).
Proof. exact (MK_COMB (@lem3704171 A B) (@lem3704170 A B)). Qed.
Lemma lem3704173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3704174 {A B : Type'} : (term10 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem3704173) (@lem3704172 A B)). Qed.
Lemma lem3704175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3704176 {A B : Type'} : (term41 A B) = (term41 A B).
Proof. exact (MK_COMB (@lem3704175) (@lem3704174 A B)). Qed.
Lemma lem3704177 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem3704176 A B) (@lem3704150 A B)). Qed.
Lemma lem3704362 {A B : Type'} : (term16 A B) = (term42 A B).
Proof. exact (TRANS (@lem3703999 A B) (@lem3704177 A B)). Qed.
Lemma lem3704363 {A B : Type'} : (term42 A B) = (term16 A B).
Proof. exact (SYM (@lem3704362 A B)). Qed.
Lemma lem3704364 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem3704366 {B : Type'} (h1 : term15 B) : term15 B.
Proof. exact (h1). Qed.
Lemma lem3704370 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem3704371 {A B : Type'} (h1 : term11 A B) : term11 A B.
Proof. exact (h1). Qed.
Lemma lem3704372 {B : Type'} (h1 : term12 B) : term12 B.
Proof. exact (h1). Qed.
Lemma lem3704385 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term80 A B s f t) = (term81 A B s f t).
Proof. exact (@lem17045 (@SUBSET A t s) ((@IMAGE A B f s) = (@IMAGE A B f t))). Qed.
Lemma lem3704390 {A : Type'} (t : A -> Prop) : (term82 A t) = (term82 A t).
Proof. exact (eq_refl (term82 A t)). Qed.
Lemma lem3704391 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term83 A B s f t) = (term84 A B s f t).
Proof. exact (MK_COMB (@lem3704390 A t) (@lem3704385 A B s f t)). Qed.
Lemma lem3704392 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term85 A B s f t) = (term83 A B s f t).
Proof. exact (@lem17045 (@FINITE A t) (term86 A B s f t)). Qed.
Lemma lem3704393 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term85 A B s f t) = (term84 A B s f t).
Proof. exact (TRANS (@lem3704392 A B s f t) (@lem3704391 A B s f t)). Qed.
Lemma lem3704396 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term72 A B s f t) = (term72 A B s f t).
Proof. exact (eq_refl (term72 A B s f t)). Qed.
Lemma lem3704397 {A : Type'} (P : type686 A) : (term87 A P) = (term88 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3704398 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term89 A B s f) = (term90 A B s f).
Proof. exact (@lem3704397 A (term73 A B s f)). Qed.
Lemma lem3704399 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term91 A B s f t) = (term72 A B s f t).
Proof. exact (eq_refl (term91 A B s f t)). Qed.
Lemma lem3704400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3704401 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term92 A B s f t) = (term85 A B s f t).
Proof. exact (MK_COMB (@lem3704400) (@lem3704399 A B s f t)). Qed.
Lemma lem3704402 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term92 A B s f t) = (term84 A B s f t).
Proof. exact (TRANS (@lem3704401 A B s f t) (@lem3704393 A B s f t)). Qed.
Lemma lem3704403 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term93 A B s f) = (term94 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704402 A B s f t)). Qed.
Lemma lem3704404 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3704405 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term90 A B s f) = (term95 A B s f).
Proof. exact (MK_COMB (@lem3704404 A) (@lem3704403 A B s f)). Qed.
Lemma lem3704406 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term89 A B s f) = (term95 A B s f).
Proof. exact (TRANS (@lem3704398 A B s f) (@lem3704405 A B s f)). Qed.
Lemma lem3704407 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term73 A B s f) = (term73 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704396 A B s f t)). Qed.
Lemma lem3704408 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704409 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term74 A B s f) = (term74 A B s f).
Proof. exact (MK_COMB (@lem3704408 A) (@lem3704407 A B s f)). Qed.
Lemma lem3704411 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term96 A B f s) = (term96 A B f s).
Proof. exact (eq_refl (term96 A B f s)). Qed.
Lemma lem3704412 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term97 A B s f) = (term97 A B s f).
Proof. exact (MK_COMB (@lem3704411 A B f s) (@lem3704409 A B s f)). Qed.
Lemma lem3704414 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term98 A B f s) = (term98 A B f s).
Proof. exact (eq_refl (term98 A B f s)). Qed.
Lemma lem3704415 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term99 A B s f) = (term100 A B s f).
Proof. exact (MK_COMB (@lem3704414 A B f s) (@lem3704406 A B s f)). Qed.
Lemma lem3704416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704417 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term101 A B s f) = (term102 A B s f).
Proof. exact (MK_COMB (@lem3704416) (@lem3704415 A B s f)). Qed.
Lemma lem3704418 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term103 A B s f) = (term104 A B s f).
Proof. exact (MK_COMB (@lem3704417 A B s f) (@lem3704412 A B s f)). Qed.
Lemma lem3704419 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term105 A B s f) = (term103 A B s f).
Proof. exact (@lem17646 (term76 A B f s) (term74 A B s f)). Qed.
Lemma lem3704420 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term105 A B s f) = (term104 A B s f).
Proof. exact (TRANS (@lem3704419 A B s f) (@lem3704418 A B s f)). Qed.
Lemma lem3704421 {A : Type'} (P : type686 A) : (term106 A P) = (term107 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3704422 {A B : Type'} (f : A -> B) : (term108 A B f) = (term109 A B f).
Proof. exact (@lem3704421 A (term77 A B f)). Qed.
Lemma lem3704423 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term110 A B f s) = ((term76 A B f s) = (term74 A B s f)).
Proof. exact (eq_refl (term110 A B f s)). Qed.
Lemma lem3704424 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3704425 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term111 A B f s) = (term105 A B s f).
Proof. exact (MK_COMB (@lem3704424) (@lem3704423 A B s f)). Qed.
Lemma lem3704426 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term111 A B f s) = (term104 A B s f).
Proof. exact (TRANS (@lem3704425 A B s f) (@lem3704420 A B s f)). Qed.
Lemma lem3704427 {A B : Type'} (f : A -> B) : (term112 A B f) = (term113 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704426 A B s f)). Qed.
Lemma lem3704428 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704429 {A B : Type'} (f : A -> B) : (term109 A B f) = (term114 A B f).
Proof. exact (MK_COMB (@lem3704428 A) (@lem3704427 A B f)). Qed.
Lemma lem3704430 {A B : Type'} (f : A -> B) : (term108 A B f) = (term114 A B f).
Proof. exact (TRANS (@lem3704422 A B f) (@lem3704429 A B f)). Qed.
Lemma lem3704431 {A B : Type'} (P : type572 A B) : (term115 A B P) = (term116 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem3704432 {A B : Type'} : (term10 A B) = (term117 A B).
Proof. exact (@lem3704431 A B (term79 A B)). Qed.
Lemma lem3704433 {A B : Type'} (f : A -> B) : (term118 A B f) = (term78 A B f).
Proof. exact (eq_refl (term118 A B f)). Qed.
Lemma lem3704434 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3704435 {A B : Type'} (f : A -> B) : (term119 A B f) = (term108 A B f).
Proof. exact (MK_COMB (@lem3704434) (@lem3704433 A B f)). Qed.
Lemma lem3704436 {A B : Type'} (f : A -> B) : (term119 A B f) = (term114 A B f).
Proof. exact (TRANS (@lem3704435 A B f) (@lem3704430 A B f)). Qed.
Lemma lem3704437 {A B : Type'} : (term120 A B) = (term121 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704436 A B f)). Qed.
Lemma lem3704438 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704439 {A B : Type'} : (term117 A B) = (term122 A B).
Proof. exact (MK_COMB (@lem3704438 A B) (@lem3704437 A B)). Qed.
Lemma lem3704440 {A B : Type'} : (term10 A B) = (term122 A B).
Proof. exact (TRANS (@lem3704432 A B) (@lem3704439 A B)). Qed.
Lemma lem3704446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3704447 {A : Type'} (P : type686 A) (Q : type686 A) : (term125 A P Q) = (term126 A P Q).
Proof. exact (@lem3704446 (A -> Prop) P Q). Qed.
Lemma lem3704448 {A B : Type'} (f : A -> B) : (term127 A B f) = (term128 A B f).
Proof. exact (@lem3704447 A (term129 A B f) (term130 A B f)). Qed.
Lemma lem3704449 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term131 A B f s) = (term100 A B s f).
Proof. exact (eq_refl (term131 A B f s)). Qed.
Lemma lem3704450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704451 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term132 A B f s) = (term102 A B s f).
Proof. exact (MK_COMB (@lem3704450) (@lem3704449 A B s f)). Qed.
Lemma lem3704452 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term133 A B f s) = (term97 A B s f).
Proof. exact (eq_refl (term133 A B f s)). Qed.
Lemma lem3704453 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term134 A B f s) = (term104 A B s f).
Proof. exact (MK_COMB (@lem3704451 A B s f) (@lem3704452 A B s f)). Qed.
Lemma lem3704454 {A B : Type'} (f : A -> B) : (term135 A B f) = (term113 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704453 A B s f)). Qed.
Lemma lem3704455 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704456 {A B : Type'} (f : A -> B) : (term127 A B f) = (term114 A B f).
Proof. exact (MK_COMB (@lem3704455 A) (@lem3704454 A B f)). Qed.
Lemma lem3704457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3704458 {A B : Type'} (f : A -> B) : (term136 A B f) = (term137 A B f).
Proof. exact (MK_COMB (@lem3704457) (@lem3704456 A B f)). Qed.
Lemma lem3704459 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term131 A B f s) = (term100 A B s f).
Proof. exact (eq_refl (term131 A B f s)). Qed.
Lemma lem3704460 {A B : Type'} (f : A -> B) : (term138 A B f) = (term129 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704459 A B s f)). Qed.
Lemma lem3704461 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704462 {A B : Type'} (f : A -> B) : (term139 A B f) = (term140 A B f).
Proof. exact (MK_COMB (@lem3704461 A) (@lem3704460 A B f)). Qed.
Lemma lem3704463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704464 {A B : Type'} (f : A -> B) : (term141 A B f) = (term142 A B f).
Proof. exact (MK_COMB (@lem3704463) (@lem3704462 A B f)). Qed.
Lemma lem3704465 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term133 A B f s) = (term97 A B s f).
Proof. exact (eq_refl (term133 A B f s)). Qed.
Lemma lem3704466 {A B : Type'} (f : A -> B) : (term143 A B f) = (term130 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704465 A B s f)). Qed.
Lemma lem3704467 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704468 {A B : Type'} (f : A -> B) : (term144 A B f) = (term145 A B f).
Proof. exact (MK_COMB (@lem3704467 A) (@lem3704466 A B f)). Qed.
Lemma lem3704469 {A B : Type'} (f : A -> B) : (term128 A B f) = (term146 A B f).
Proof. exact (MK_COMB (@lem3704464 A B f) (@lem3704468 A B f)). Qed.
Lemma lem3704470 {A B : Type'} (f : A -> B) : ((term127 A B f) = (term128 A B f)) = ((term114 A B f) = (term146 A B f)).
Proof. exact (MK_COMB (@lem3704458 A B f) (@lem3704469 A B f)). Qed.
Lemma lem3704471 {A B : Type'} (f : A -> B) : (term114 A B f) = (term146 A B f).
Proof. exact (EQ_MP (@lem3704470 A B f) (@lem3704448 A B f)). Qed.
Lemma lem3704644 {A B : Type'} : (term121 A B) = (term147 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704471 A B f)). Qed.
Lemma lem3704645 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704646 {A B : Type'} : (term122 A B) = (term148 A B).
Proof. exact (MK_COMB (@lem3704645 A B) (@lem3704644 A B)). Qed.
Lemma lem3704648 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3704649 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term149 A B P Q) = (term150 A B P Q).
Proof. exact (@lem3704648 (A -> B) P Q). Qed.
Lemma lem3704650 {A B : Type'} : (term151 A B) = (term152 A B).
Proof. exact (@lem3704649 A B (term153 A B) (term154 A B)). Qed.
Lemma lem3704651 {A B : Type'} (f : A -> B) : (term155 A B f) = (term140 A B f).
Proof. exact (eq_refl (term155 A B f)). Qed.
Lemma lem3704652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704653 {A B : Type'} (f : A -> B) : (term156 A B f) = (term142 A B f).
Proof. exact (MK_COMB (@lem3704652) (@lem3704651 A B f)). Qed.
Lemma lem3704654 {A B : Type'} (f : A -> B) : (term157 A B f) = (term145 A B f).
Proof. exact (eq_refl (term157 A B f)). Qed.
Lemma lem3704655 {A B : Type'} (f : A -> B) : (term158 A B f) = (term146 A B f).
Proof. exact (MK_COMB (@lem3704653 A B f) (@lem3704654 A B f)). Qed.
Lemma lem3704656 {A B : Type'} : (term159 A B) = (term147 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704655 A B f)). Qed.
Lemma lem3704657 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704658 {A B : Type'} : (term151 A B) = (term148 A B).
Proof. exact (MK_COMB (@lem3704657 A B) (@lem3704656 A B)). Qed.
Lemma lem3704659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3704660 {A B : Type'} : (term160 A B) = (term161 A B).
Proof. exact (MK_COMB (@lem3704659) (@lem3704658 A B)). Qed.
Lemma lem3704661 {A B : Type'} (f : A -> B) : (term155 A B f) = (term140 A B f).
Proof. exact (eq_refl (term155 A B f)). Qed.
Lemma lem3704662 {A B : Type'} : (term162 A B) = (term153 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704661 A B f)). Qed.
Lemma lem3704663 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704664 {A B : Type'} : (term163 A B) = (term164 A B).
Proof. exact (MK_COMB (@lem3704663 A B) (@lem3704662 A B)). Qed.
Lemma lem3704665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704666 {A B : Type'} : (term165 A B) = (term166 A B).
Proof. exact (MK_COMB (@lem3704665) (@lem3704664 A B)). Qed.
Lemma lem3704667 {A B : Type'} (f : A -> B) : (term157 A B f) = (term145 A B f).
Proof. exact (eq_refl (term157 A B f)). Qed.
Lemma lem3704668 {A B : Type'} : (term167 A B) = (term154 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704667 A B f)). Qed.
Lemma lem3704669 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704670 {A B : Type'} : (term168 A B) = (term169 A B).
Proof. exact (MK_COMB (@lem3704669 A B) (@lem3704668 A B)). Qed.
Lemma lem3704671 {A B : Type'} : (term152 A B) = (term170 A B).
Proof. exact (MK_COMB (@lem3704666 A B) (@lem3704670 A B)). Qed.
Lemma lem3704672 {A B : Type'} : ((term151 A B) = (term152 A B)) = ((term148 A B) = (term170 A B)).
Proof. exact (MK_COMB (@lem3704660 A B) (@lem3704671 A B)). Qed.
Lemma lem3704673 {A B : Type'} : (term148 A B) = (term170 A B).
Proof. exact (EQ_MP (@lem3704672 A B) (@lem3704650 A B)). Qed.
Lemma lem3704854 {A B : Type'} : (term122 A B) = (term170 A B).
Proof. exact (TRANS (@lem3704646 A B) (@lem3704673 A B)). Qed.
Lemma lem3704856 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3704857 {A : Type'} (P : Prop) (Q : type686 A) : (term173 A P Q) = (term174 A P Q).
Proof. exact (@lem3704856 (A -> Prop) P Q). Qed.
Lemma lem3704858 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term175 A B s f) = (term176 A B s f).
Proof. exact (@lem3704857 A (term177 A B f s) (term73 A B s f)). Qed.
Lemma lem3704859 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term91 A B s f t) = (term72 A B s f t).
Proof. exact (eq_refl (term91 A B s f t)). Qed.
Lemma lem3704860 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term178 A B s f) = (term73 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704859 A B s f t)). Qed.
Lemma lem3704861 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704862 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term179 A B s f) = (term74 A B s f).
Proof. exact (MK_COMB (@lem3704861 A) (@lem3704860 A B s f)). Qed.
Lemma lem3704863 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term96 A B f s) = (term96 A B f s).
Proof. exact (eq_refl (term96 A B f s)). Qed.
Lemma lem3704864 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term175 A B s f) = (term97 A B s f).
Proof. exact (MK_COMB (@lem3704863 A B f s) (@lem3704862 A B s f)). Qed.
Lemma lem3704865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3704866 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term180 A B s f) = (term181 A B s f).
Proof. exact (MK_COMB (@lem3704865) (@lem3704864 A B s f)). Qed.
Lemma lem3704867 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term91 A B s f t) = (term72 A B s f t).
Proof. exact (eq_refl (term91 A B s f t)). Qed.
Lemma lem3704868 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term96 A B f s) = (term96 A B f s).
Proof. exact (eq_refl (term96 A B f s)). Qed.
Lemma lem3704869 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term182 A B s f t) = (term183 A B s f t).
Proof. exact (MK_COMB (@lem3704868 A B f s) (@lem3704867 A B s f t)). Qed.
Lemma lem3704870 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term184 A B s f) = (term185 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704869 A B s f t)). Qed.
Lemma lem3704871 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704872 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term176 A B s f) = (term186 A B s f).
Proof. exact (MK_COMB (@lem3704871 A) (@lem3704870 A B s f)). Qed.
Lemma lem3704873 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term175 A B s f) = (term176 A B s f)) = ((term97 A B s f) = (term186 A B s f)).
Proof. exact (MK_COMB (@lem3704866 A B s f) (@lem3704872 A B s f)). Qed.
Lemma lem3704874 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term97 A B s f) = (term186 A B s f).
Proof. exact (EQ_MP (@lem3704873 A B s f) (@lem3704858 A B s f)). Qed.
Lemma lem3704875 {A B : Type'} (f : A -> B) : (term130 A B f) = (term187 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704874 A B s f)). Qed.
Lemma lem3704876 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704877 {A B : Type'} (f : A -> B) : (term145 A B f) = (term188 A B f).
Proof. exact (MK_COMB (@lem3704876 A) (@lem3704875 A B f)). Qed.
Lemma lem3704878 {A B : Type'} : (term154 A B) = (term189 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704877 A B f)). Qed.
Lemma lem3704879 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704880 {A B : Type'} : (term169 A B) = (term190 A B).
Proof. exact (MK_COMB (@lem3704879 A B) (@lem3704878 A B)). Qed.
Lemma lem3704881 {A B : Type'} : (term166 A B) = (term166 A B).
Proof. exact (eq_refl (term166 A B)). Qed.
Lemma lem3704882 {A B : Type'} : (term170 A B) = (term191 A B).
Proof. exact (MK_COMB (@lem3704881 A B) (@lem3704880 A B)). Qed.
Lemma lem3704884 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term124 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3704885 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term150 A B P Q) = (term149 A B P Q).
Proof. exact (@lem3704884 (A -> B) P Q). Qed.
Lemma lem3704886 {A B : Type'} : (term192 A B) = (term193 A B).
Proof. exact (@lem3704885 A B (term153 A B) (term189 A B)). Qed.
Lemma lem3704887 {A B : Type'} (f : A -> B) : (term155 A B f) = (term140 A B f).
Proof. exact (eq_refl (term155 A B f)). Qed.
Lemma lem3704888 {A B : Type'} : (term162 A B) = (term153 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704887 A B f)). Qed.
Lemma lem3704889 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704890 {A B : Type'} : (term163 A B) = (term164 A B).
Proof. exact (MK_COMB (@lem3704889 A B) (@lem3704888 A B)). Qed.
Lemma lem3704891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704892 {A B : Type'} : (term165 A B) = (term166 A B).
Proof. exact (MK_COMB (@lem3704891) (@lem3704890 A B)). Qed.
Lemma lem3704893 {A B : Type'} (f : A -> B) : (term194 A B f) = (term188 A B f).
Proof. exact (eq_refl (term194 A B f)). Qed.
Lemma lem3704894 {A B : Type'} : (term195 A B) = (term189 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704893 A B f)). Qed.
Lemma lem3704895 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704896 {A B : Type'} : (term196 A B) = (term190 A B).
Proof. exact (MK_COMB (@lem3704895 A B) (@lem3704894 A B)). Qed.
Lemma lem3704897 {A B : Type'} : (term192 A B) = (term191 A B).
Proof. exact (MK_COMB (@lem3704892 A B) (@lem3704896 A B)). Qed.
Lemma lem3704898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3704899 {A B : Type'} : (term197 A B) = (term198 A B).
Proof. exact (MK_COMB (@lem3704898) (@lem3704897 A B)). Qed.
Lemma lem3704900 {A B : Type'} (f : A -> B) : (term155 A B f) = (term140 A B f).
Proof. exact (eq_refl (term155 A B f)). Qed.
Lemma lem3704901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704902 {A B : Type'} (f : A -> B) : (term156 A B f) = (term142 A B f).
Proof. exact (MK_COMB (@lem3704901) (@lem3704900 A B f)). Qed.
Lemma lem3704903 {A B : Type'} (f : A -> B) : (term194 A B f) = (term188 A B f).
Proof. exact (eq_refl (term194 A B f)). Qed.
Lemma lem3704904 {A B : Type'} (f : A -> B) : (term199 A B f) = (term200 A B f).
Proof. exact (MK_COMB (@lem3704902 A B f) (@lem3704903 A B f)). Qed.
Lemma lem3704905 {A B : Type'} : (term201 A B) = (term202 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704904 A B f)). Qed.
Lemma lem3704906 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704907 {A B : Type'} : (term193 A B) = (term203 A B).
Proof. exact (MK_COMB (@lem3704906 A B) (@lem3704905 A B)). Qed.
Lemma lem3704908 {A B : Type'} : ((term192 A B) = (term193 A B)) = ((term191 A B) = (term203 A B)).
Proof. exact (MK_COMB (@lem3704899 A B) (@lem3704907 A B)). Qed.
Lemma lem3704909 {A B : Type'} : (term191 A B) = (term203 A B).
Proof. exact (EQ_MP (@lem3704908 A B) (@lem3704886 A B)). Qed.
Lemma lem3704911 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term124 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3704912 {A : Type'} (P : type686 A) (Q : type686 A) : (term126 A P Q) = (term125 A P Q).
Proof. exact (@lem3704911 (A -> Prop) P Q). Qed.
Lemma lem3704913 {A B : Type'} (f : A -> B) : (term204 A B f) = (term205 A B f).
Proof. exact (@lem3704912 A (term129 A B f) (term187 A B f)). Qed.
Lemma lem3704914 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term131 A B f s) = (term100 A B s f).
Proof. exact (eq_refl (term131 A B f s)). Qed.
Lemma lem3704915 {A B : Type'} (f : A -> B) : (term138 A B f) = (term129 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704914 A B s f)). Qed.
Lemma lem3704916 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704917 {A B : Type'} (f : A -> B) : (term139 A B f) = (term140 A B f).
Proof. exact (MK_COMB (@lem3704916 A) (@lem3704915 A B f)). Qed.
Lemma lem3704918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704919 {A B : Type'} (f : A -> B) : (term141 A B f) = (term142 A B f).
Proof. exact (MK_COMB (@lem3704918) (@lem3704917 A B f)). Qed.
Lemma lem3704920 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term206 A B f s) = (term186 A B s f).
Proof. exact (eq_refl (term206 A B f s)). Qed.
Lemma lem3704921 {A B : Type'} (f : A -> B) : (term207 A B f) = (term187 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704920 A B s f)). Qed.
Lemma lem3704922 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704923 {A B : Type'} (f : A -> B) : (term208 A B f) = (term188 A B f).
Proof. exact (MK_COMB (@lem3704922 A) (@lem3704921 A B f)). Qed.
Lemma lem3704924 {A B : Type'} (f : A -> B) : (term204 A B f) = (term200 A B f).
Proof. exact (MK_COMB (@lem3704919 A B f) (@lem3704923 A B f)). Qed.
Lemma lem3704925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3704926 {A B : Type'} (f : A -> B) : (term209 A B f) = (term210 A B f).
Proof. exact (MK_COMB (@lem3704925) (@lem3704924 A B f)). Qed.
Lemma lem3704927 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term131 A B f s) = (term100 A B s f).
Proof. exact (eq_refl (term131 A B f s)). Qed.
Lemma lem3704928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3704929 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term132 A B f s) = (term102 A B s f).
Proof. exact (MK_COMB (@lem3704928) (@lem3704927 A B s f)). Qed.
Lemma lem3704930 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term206 A B f s) = (term186 A B s f).
Proof. exact (eq_refl (term206 A B f s)). Qed.
Lemma lem3704931 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term211 A B f s) = (term212 A B s f).
Proof. exact (MK_COMB (@lem3704929 A B s f) (@lem3704930 A B s f)). Qed.
Lemma lem3704932 {A B : Type'} (f : A -> B) : (term213 A B f) = (term214 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704931 A B s f)). Qed.
Lemma lem3704933 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704934 {A B : Type'} (f : A -> B) : (term205 A B f) = (term215 A B f).
Proof. exact (MK_COMB (@lem3704933 A) (@lem3704932 A B f)). Qed.
Lemma lem3704935 {A B : Type'} (f : A -> B) : ((term204 A B f) = (term205 A B f)) = ((term200 A B f) = (term215 A B f)).
Proof. exact (MK_COMB (@lem3704926 A B f) (@lem3704934 A B f)). Qed.
Lemma lem3704936 {A B : Type'} (f : A -> B) : (term200 A B f) = (term215 A B f).
Proof. exact (EQ_MP (@lem3704935 A B f) (@lem3704913 A B f)). Qed.
Lemma lem3704938 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3704939 {A : Type'} (P : Prop) (Q : type686 A) : (term218 A P Q) = (term219 A P Q).
Proof. exact (@lem3704938 (A -> Prop) P Q). Qed.
Lemma lem3704940 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term220 A B s f) = (term221 A B s f).
Proof. exact (@lem3704939 A (term100 A B s f) (term185 A B s f)). Qed.
Lemma lem3704941 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term222 A B s f t) = (term183 A B s f t).
Proof. exact (eq_refl (term222 A B s f t)). Qed.
Lemma lem3704942 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term223 A B s f) = (term185 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704941 A B s f t)). Qed.
Lemma lem3704943 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704944 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term224 A B s f) = (term186 A B s f).
Proof. exact (MK_COMB (@lem3704943 A) (@lem3704942 A B s f)). Qed.
Lemma lem3704945 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term102 A B s f) = (term102 A B s f).
Proof. exact (eq_refl (term102 A B s f)). Qed.
Lemma lem3704946 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term220 A B s f) = (term212 A B s f).
Proof. exact (MK_COMB (@lem3704945 A B s f) (@lem3704944 A B s f)). Qed.
Lemma lem3704947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3704948 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term225 A B s f) = (term226 A B s f).
Proof. exact (MK_COMB (@lem3704947) (@lem3704946 A B s f)). Qed.
Lemma lem3704949 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term222 A B s f t) = (term183 A B s f t).
Proof. exact (eq_refl (term222 A B s f t)). Qed.
Lemma lem3704950 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term102 A B s f) = (term102 A B s f).
Proof. exact (eq_refl (term102 A B s f)). Qed.
Lemma lem3704951 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term227 A B s f t) = (term228 A B s f t).
Proof. exact (MK_COMB (@lem3704950 A B s f) (@lem3704949 A B s f t)). Qed.
Lemma lem3704952 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term229 A B s f) = (term230 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3704951 A B s f t)). Qed.
Lemma lem3704953 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704954 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term221 A B s f) = (term231 A B s f).
Proof. exact (MK_COMB (@lem3704953 A) (@lem3704952 A B s f)). Qed.
Lemma lem3704955 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term220 A B s f) = (term221 A B s f)) = ((term212 A B s f) = (term231 A B s f)).
Proof. exact (MK_COMB (@lem3704948 A B s f) (@lem3704954 A B s f)). Qed.
Lemma lem3704956 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term212 A B s f) = (term231 A B s f).
Proof. exact (EQ_MP (@lem3704955 A B s f) (@lem3704940 A B s f)). Qed.
Lemma lem3704957 {A B : Type'} (f : A -> B) : (term214 A B f) = (term232 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3704956 A B s f)). Qed.
Lemma lem3704958 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3704959 {A B : Type'} (f : A -> B) : (term215 A B f) = (term233 A B f).
Proof. exact (MK_COMB (@lem3704958 A) (@lem3704957 A B f)). Qed.
Lemma lem3704960 {A B : Type'} (f : A -> B) : (term200 A B f) = (term233 A B f).
Proof. exact (TRANS (@lem3704936 A B f) (@lem3704959 A B f)). Qed.
Lemma lem3704961 {A B : Type'} : (term202 A B) = (term234 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3704960 A B f)). Qed.
Lemma lem3704962 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3704963 {A B : Type'} : (term203 A B) = (term235 A B).
Proof. exact (MK_COMB (@lem3704962 A B) (@lem3704961 A B)). Qed.
Lemma lem3704964 {A B : Type'} : (term191 A B) = (term235 A B).
Proof. exact (TRANS (@lem3704909 A B) (@lem3704963 A B)). Qed.
Lemma lem3704965 {A B : Type'} : (term170 A B) = (term235 A B).
Proof. exact (TRANS (@lem3704882 A B) (@lem3704964 A B)). Qed.
Lemma lem3704966 {A B : Type'} : (term122 A B) = (term235 A B).
Proof. exact (TRANS (@lem3704854 A B) (@lem3704965 A B)). Qed.
Lemma lem3704967 {A B : Type'} : (term10 A B) = (term235 A B).
Proof. exact (TRANS (@lem3704440 A B) (@lem3704966 A B)). Qed.
Lemma lem3704968 {A B : Type'} (h1 : term10 A B) : term235 A B.
Proof. exact (EQ_MP (@lem3704967 A B) (@lem3704364 A B h1)). Qed.
Lemma lem3704982 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3704983 {B : Type'} : (term71 B) = (term71 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3704982 B s)). Qed.
Lemma lem3704984 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3704993 {B : Type'} : (term15 B) = (term15 B).
Proof. exact (MK_COMB (@lem3704984 B) (@lem3704983 B)). Qed.
Lemma lem3704994 {B : Type'} (h1 : term15 B) : term15 B.
Proof. exact (EQ_MP (@lem3704993 B) (@lem3704366 B h1)). Qed.
Lemma lem3705213 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term236 A t f s) = (term237 A t f s).
Proof. exact (@lem17045 (@FINITE A t) (term238 A t f s)). Qed.
Lemma lem3705227 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term239 A s t f s') = (term240 A s t f s').
Proof. exact (@lem17045 (@SUBSET A s' s) (t = (@IMAGE A A f s'))). Qed.
Lemma lem3705232 {A : Type'} (s' : A -> Prop) : (term82 A s') = (term82 A s').
Proof. exact (eq_refl (term82 A s')). Qed.
Lemma lem3705233 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term241 A s t f s') = (term242 A s t f s').
Proof. exact (MK_COMB (@lem3705232 A s') (@lem3705227 A s t f s')). Qed.
Lemma lem3705234 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term243 A s t f s') = (term241 A s t f s').
Proof. exact (@lem17045 (@FINITE A s') (term244 A s t f s')). Qed.
Lemma lem3705235 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term243 A s t f s') = (term242 A s t f s').
Proof. exact (TRANS (@lem3705234 A s t f s') (@lem3705233 A s t f s')). Qed.
Lemma lem3705238 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term43 A s t f s') = (term43 A s t f s').
Proof. exact (eq_refl (term43 A s t f s')). Qed.
Lemma lem3705239 {A : Type'} (P : type686 A) : (term87 A P) = (term88 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3705240 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term245 A s t f) = (term246 A s t f).
Proof. exact (@lem3705239 A (term44 A s t f)). Qed.
Lemma lem3705241 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term247 A s t f s') = (term43 A s t f s').
Proof. exact (eq_refl (term247 A s t f s')). Qed.
Lemma lem3705242 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3705243 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term248 A s t f s') = (term243 A s t f s').
Proof. exact (MK_COMB (@lem3705242) (@lem3705241 A s t f s')). Qed.
Lemma lem3705244 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term248 A s t f s') = (term242 A s t f s').
Proof. exact (TRANS (@lem3705243 A s t f s') (@lem3705235 A s t f s')). Qed.
Lemma lem3705245 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term249 A s t f) = (term250 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3705244 A s t f s')). Qed.
Lemma lem3705246 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705247 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term246 A s t f) = (term251 A s t f).
Proof. exact (MK_COMB (@lem3705246 A) (@lem3705245 A s t f)). Qed.
Lemma lem3705248 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term245 A s t f) = (term251 A s t f).
Proof. exact (TRANS (@lem3705240 A s t f) (@lem3705247 A s t f)). Qed.
Lemma lem3705249 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term44 A s t f) = (term44 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3705238 A s t f s')). Qed.
Lemma lem3705250 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3705251 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term45 A s t f) = (term45 A s t f).
Proof. exact (MK_COMB (@lem3705250 A) (@lem3705249 A s t f)). Qed.
Lemma lem3705252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3705253 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term252 A t f s) = (term253 A t f s).
Proof. exact (MK_COMB (@lem3705252) (@lem3705213 A t f s)). Qed.
Lemma lem3705254 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term254 A s t f) = (term255 A s t f).
Proof. exact (MK_COMB (@lem3705253 A t f s) (@lem3705251 A s t f)). Qed.
Lemma lem3705256 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term256 A t f s) = (term256 A t f s).
Proof. exact (eq_refl (term256 A t f s)). Qed.
Lemma lem3705257 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term257 A s t f) = (term258 A s t f).
Proof. exact (MK_COMB (@lem3705256 A t f s) (@lem3705248 A s t f)). Qed.
Lemma lem3705258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3705259 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term259 A s t f) = (term260 A s t f).
Proof. exact (MK_COMB (@lem3705258) (@lem3705257 A s t f)). Qed.
Lemma lem3705260 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term261 A s t f) = (term262 A s t f).
Proof. exact (MK_COMB (@lem3705259 A s t f) (@lem3705254 A s t f)). Qed.
Lemma lem3705261 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term47 A t f s) = (term45 A s t f)) = (term261 A s t f).
Proof. exact (@lem17784 (term47 A t f s) (term45 A s t f)). Qed.
Lemma lem3705262 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term47 A t f s) = (term45 A s t f)) = (term262 A s t f).
Proof. exact (TRANS (@lem3705261 A s t f) (@lem3705260 A s t f)). Qed.
Lemma lem3705263 {A : Type'} (s : A -> Prop) (f : A -> A) : (term48 A s f) = (term263 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3705262 A s t f)). Qed.
Lemma lem3705264 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705265 {A : Type'} (s : A -> Prop) (f : A -> A) : (term49 A s f) = (term264 A s f).
Proof. exact (MK_COMB (@lem3705264 A) (@lem3705263 A s f)). Qed.
Lemma lem3705266 {A : Type'} (f : A -> A) : (term50 A f) = (term265 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705265 A s f)). Qed.
Lemma lem3705267 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705268 {A : Type'} (f : A -> A) : (term51 A f) = (term266 A f).
Proof. exact (MK_COMB (@lem3705267 A) (@lem3705266 A f)). Qed.
Lemma lem3705269 {A : Type'} : (term52 A) = (term267 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3705268 A f)). Qed.
Lemma lem3705270 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3705271 {A : Type'} : (term12 A) = (term268 A).
Proof. exact (MK_COMB (@lem3705270 A) (@lem3705269 A)). Qed.
Lemma lem3705281 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3705282 {A : Type'} (P : type686 A) (Q : type686 A) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem3705281 (A -> Prop) P Q). Qed.
Lemma lem3705283 {A : Type'} (s : A -> Prop) (f : A -> A) : (term273 A s f) = (term274 A s f).
Proof. exact (@lem3705282 A (term275 A s f) (term276 A s f)). Qed.
Lemma lem3705284 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term277 A s f t) = (term258 A s t f).
Proof. exact (eq_refl (term277 A s f t)). Qed.
Lemma lem3705285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3705286 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term278 A s f t) = (term260 A s t f).
Proof. exact (MK_COMB (@lem3705285) (@lem3705284 A s t f)). Qed.
Lemma lem3705287 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term279 A s f t) = (term255 A s t f).
Proof. exact (eq_refl (term279 A s f t)). Qed.
Lemma lem3705288 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term280 A s f t) = (term262 A s t f).
Proof. exact (MK_COMB (@lem3705286 A s t f) (@lem3705287 A s t f)). Qed.
Lemma lem3705289 {A : Type'} (s : A -> Prop) (f : A -> A) : (term281 A s f) = (term263 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3705288 A s t f)). Qed.
Lemma lem3705290 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705291 {A : Type'} (s : A -> Prop) (f : A -> A) : (term273 A s f) = (term264 A s f).
Proof. exact (MK_COMB (@lem3705290 A) (@lem3705289 A s f)). Qed.
Lemma lem3705292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3705293 {A : Type'} (s : A -> Prop) (f : A -> A) : (term282 A s f) = (term283 A s f).
Proof. exact (MK_COMB (@lem3705292) (@lem3705291 A s f)). Qed.
Lemma lem3705294 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term277 A s f t) = (term258 A s t f).
Proof. exact (eq_refl (term277 A s f t)). Qed.
Lemma lem3705295 {A : Type'} (s : A -> Prop) (f : A -> A) : (term284 A s f) = (term275 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3705294 A s t f)). Qed.
Lemma lem3705296 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705297 {A : Type'} (s : A -> Prop) (f : A -> A) : (term285 A s f) = (term286 A s f).
Proof. exact (MK_COMB (@lem3705296 A) (@lem3705295 A s f)). Qed.
Lemma lem3705298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3705299 {A : Type'} (s : A -> Prop) (f : A -> A) : (term287 A s f) = (term288 A s f).
Proof. exact (MK_COMB (@lem3705298) (@lem3705297 A s f)). Qed.
Lemma lem3705300 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term279 A s f t) = (term255 A s t f).
Proof. exact (eq_refl (term279 A s f t)). Qed.
Lemma lem3705301 {A : Type'} (s : A -> Prop) (f : A -> A) : (term289 A s f) = (term276 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3705300 A s t f)). Qed.
Lemma lem3705302 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705303 {A : Type'} (s : A -> Prop) (f : A -> A) : (term290 A s f) = (term291 A s f).
Proof. exact (MK_COMB (@lem3705302 A) (@lem3705301 A s f)). Qed.
Lemma lem3705304 {A : Type'} (s : A -> Prop) (f : A -> A) : (term274 A s f) = (term292 A s f).
Proof. exact (MK_COMB (@lem3705299 A s f) (@lem3705303 A s f)). Qed.
Lemma lem3705305 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term273 A s f) = (term274 A s f)) = ((term264 A s f) = (term292 A s f)).
Proof. exact (MK_COMB (@lem3705293 A s f) (@lem3705304 A s f)). Qed.
Lemma lem3705306 {A : Type'} (s : A -> Prop) (f : A -> A) : (term264 A s f) = (term292 A s f).
Proof. exact (EQ_MP (@lem3705305 A s f) (@lem3705283 A s f)). Qed.
Lemma lem3705479 {A : Type'} (f : A -> A) : (term265 A f) = (term293 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705306 A s f)). Qed.
Lemma lem3705480 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705481 {A : Type'} (f : A -> A) : (term266 A f) = (term294 A f).
Proof. exact (MK_COMB (@lem3705480 A) (@lem3705479 A f)). Qed.
Lemma lem3705483 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3705484 {A : Type'} (P : type686 A) (Q : type686 A) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem3705483 (A -> Prop) P Q). Qed.
Lemma lem3705485 {A : Type'} (f : A -> A) : (term295 A f) = (term296 A f).
Proof. exact (@lem3705484 A (term297 A f) (term298 A f)). Qed.
Lemma lem3705486 {A : Type'} (s : A -> Prop) (f : A -> A) : (term299 A f s) = (term286 A s f).
Proof. exact (eq_refl (term299 A f s)). Qed.
Lemma lem3705487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3705488 {A : Type'} (s : A -> Prop) (f : A -> A) : (term300 A f s) = (term288 A s f).
Proof. exact (MK_COMB (@lem3705487) (@lem3705486 A s f)). Qed.
Lemma lem3705489 {A : Type'} (s : A -> Prop) (f : A -> A) : (term301 A f s) = (term291 A s f).
Proof. exact (eq_refl (term301 A f s)). Qed.
Lemma lem3705490 {A : Type'} (s : A -> Prop) (f : A -> A) : (term302 A f s) = (term292 A s f).
Proof. exact (MK_COMB (@lem3705488 A s f) (@lem3705489 A s f)). Qed.
Lemma lem3705491 {A : Type'} (f : A -> A) : (term303 A f) = (term293 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705490 A s f)). Qed.
Lemma lem3705492 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705493 {A : Type'} (f : A -> A) : (term295 A f) = (term294 A f).
Proof. exact (MK_COMB (@lem3705492 A) (@lem3705491 A f)). Qed.
Lemma lem3705494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3705495 {A : Type'} (f : A -> A) : (term304 A f) = (term305 A f).
Proof. exact (MK_COMB (@lem3705494) (@lem3705493 A f)). Qed.
Lemma lem3705496 {A : Type'} (s : A -> Prop) (f : A -> A) : (term299 A f s) = (term286 A s f).
Proof. exact (eq_refl (term299 A f s)). Qed.
Lemma lem3705497 {A : Type'} (f : A -> A) : (term306 A f) = (term297 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705496 A s f)). Qed.
Lemma lem3705498 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705499 {A : Type'} (f : A -> A) : (term307 A f) = (term308 A f).
Proof. exact (MK_COMB (@lem3705498 A) (@lem3705497 A f)). Qed.
Lemma lem3705500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3705501 {A : Type'} (f : A -> A) : (term309 A f) = (term310 A f).
Proof. exact (MK_COMB (@lem3705500) (@lem3705499 A f)). Qed.
Lemma lem3705502 {A : Type'} (s : A -> Prop) (f : A -> A) : (term301 A f s) = (term291 A s f).
Proof. exact (eq_refl (term301 A f s)). Qed.
Lemma lem3705503 {A : Type'} (f : A -> A) : (term311 A f) = (term298 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705502 A s f)). Qed.
Lemma lem3705504 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705505 {A : Type'} (f : A -> A) : (term312 A f) = (term313 A f).
Proof. exact (MK_COMB (@lem3705504 A) (@lem3705503 A f)). Qed.
Lemma lem3705506 {A : Type'} (f : A -> A) : (term296 A f) = (term314 A f).
Proof. exact (MK_COMB (@lem3705501 A f) (@lem3705505 A f)). Qed.
Lemma lem3705507 {A : Type'} (f : A -> A) : ((term295 A f) = (term296 A f)) = ((term294 A f) = (term314 A f)).
Proof. exact (MK_COMB (@lem3705495 A f) (@lem3705506 A f)). Qed.
Lemma lem3705508 {A : Type'} (f : A -> A) : (term294 A f) = (term314 A f).
Proof. exact (EQ_MP (@lem3705507 A f) (@lem3705485 A f)). Qed.
Lemma lem3705689 {A : Type'} (f : A -> A) : (term266 A f) = (term314 A f).
Proof. exact (TRANS (@lem3705481 A f) (@lem3705508 A f)). Qed.
Lemma lem3705690 {A : Type'} : (term267 A) = (term315 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3705689 A f)). Qed.
Lemma lem3705691 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3705692 {A : Type'} : (term268 A) = (term316 A).
Proof. exact (MK_COMB (@lem3705691 A) (@lem3705690 A)). Qed.
Lemma lem3705694 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3705695 {A : Type'} (P : type488 A) (Q : type488 A) : (term317 A P Q) = (term318 A P Q).
Proof. exact (@lem3705694 (A -> A) P Q). Qed.
Lemma lem3705696 {A : Type'} : (term319 A) = (term320 A).
Proof. exact (@lem3705695 A (term321 A) (term322 A)). Qed.
Lemma lem3705697 {A : Type'} (f : A -> A) : (term323 A f) = (term308 A f).
Proof. exact (eq_refl (term323 A f)). Qed.
Lemma lem3705698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3705699 {A : Type'} (f : A -> A) : (term324 A f) = (term310 A f).
Proof. exact (MK_COMB (@lem3705698) (@lem3705697 A f)). Qed.
Lemma lem3705700 {A : Type'} (f : A -> A) : (term325 A f) = (term313 A f).
Proof. exact (eq_refl (term325 A f)). Qed.
Lemma lem3705701 {A : Type'} (f : A -> A) : (term326 A f) = (term314 A f).
Proof. exact (MK_COMB (@lem3705699 A f) (@lem3705700 A f)). Qed.
Lemma lem3705702 {A : Type'} : (term327 A) = (term315 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3705701 A f)). Qed.
Lemma lem3705703 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3705704 {A : Type'} : (term319 A) = (term316 A).
Proof. exact (MK_COMB (@lem3705703 A) (@lem3705702 A)). Qed.
Lemma lem3705705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3705706 {A : Type'} : (term328 A) = (term329 A).
Proof. exact (MK_COMB (@lem3705705) (@lem3705704 A)). Qed.
Lemma lem3705707 {A : Type'} (f : A -> A) : (term323 A f) = (term308 A f).
Proof. exact (eq_refl (term323 A f)). Qed.
Lemma lem3705708 {A : Type'} : (term330 A) = (term321 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3705707 A f)). Qed.
Lemma lem3705709 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3705710 {A : Type'} : (term331 A) = (term332 A).
Proof. exact (MK_COMB (@lem3705709 A) (@lem3705708 A)). Qed.
Lemma lem3705711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3705712 {A : Type'} : (term333 A) = (term334 A).
Proof. exact (MK_COMB (@lem3705711) (@lem3705710 A)). Qed.
Lemma lem3705713 {A : Type'} (f : A -> A) : (term325 A f) = (term313 A f).
Proof. exact (eq_refl (term325 A f)). Qed.
Lemma lem3705714 {A : Type'} : (term335 A) = (term322 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3705713 A f)). Qed.
Lemma lem3705715 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3705716 {A : Type'} : (term336 A) = (term337 A).
Proof. exact (MK_COMB (@lem3705715 A) (@lem3705714 A)). Qed.
Lemma lem3705717 {A : Type'} : (term320 A) = (term338 A).
Proof. exact (MK_COMB (@lem3705712 A) (@lem3705716 A)). Qed.
Lemma lem3705718 {A : Type'} : ((term319 A) = (term320 A)) = ((term316 A) = (term338 A)).
Proof. exact (MK_COMB (@lem3705706 A) (@lem3705717 A)). Qed.
Lemma lem3705719 {A : Type'} : (term316 A) = (term338 A).
Proof. exact (EQ_MP (@lem3705718 A) (@lem3705696 A)). Qed.
Lemma lem3705908 {A : Type'} : (term268 A) = (term338 A).
Proof. exact (TRANS (@lem3705692 A) (@lem3705719 A)). Qed.
Lemma lem3705910 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3705911 {A : Type'} (P : Prop) (Q : type686 A) : (term218 A P Q) = (term219 A P Q).
Proof. exact (@lem3705910 (A -> Prop) P Q). Qed.
Lemma lem3705912 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term339 A s t f) = (term340 A s t f).
Proof. exact (@lem3705911 A (term237 A t f s) (term44 A s t f)). Qed.
Lemma lem3705913 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term247 A s t f s') = (term43 A s t f s').
Proof. exact (eq_refl (term247 A s t f s')). Qed.
Lemma lem3705914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term341 A s t f) = (term44 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3705913 A s t f s')). Qed.
Lemma lem3705915 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3705916 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term342 A s t f) = (term45 A s t f).
Proof. exact (MK_COMB (@lem3705915 A) (@lem3705914 A s t f)). Qed.
Lemma lem3705917 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term253 A t f s) = (term253 A t f s).
Proof. exact (eq_refl (term253 A t f s)). Qed.
Lemma lem3705918 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term339 A s t f) = (term255 A s t f).
Proof. exact (MK_COMB (@lem3705917 A t f s) (@lem3705916 A s t f)). Qed.
Lemma lem3705919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3705920 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term343 A s t f) = (term344 A s t f).
Proof. exact (MK_COMB (@lem3705919) (@lem3705918 A s t f)). Qed.
Lemma lem3705921 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term247 A s t f s') = (term43 A s t f s').
Proof. exact (eq_refl (term247 A s t f s')). Qed.
Lemma lem3705922 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term253 A t f s) = (term253 A t f s).
Proof. exact (eq_refl (term253 A t f s)). Qed.
Lemma lem3705923 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term345 A s t f s') = (term346 A s t f s').
Proof. exact (MK_COMB (@lem3705922 A t f s) (@lem3705921 A s t f s')). Qed.
Lemma lem3705924 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term347 A s t f) = (term348 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3705923 A s t f s')). Qed.
Lemma lem3705925 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3705926 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term340 A s t f) = (term349 A s t f).
Proof. exact (MK_COMB (@lem3705925 A) (@lem3705924 A s t f)). Qed.
Lemma lem3705927 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term339 A s t f) = (term340 A s t f)) = ((term255 A s t f) = (term349 A s t f)).
Proof. exact (MK_COMB (@lem3705920 A s t f) (@lem3705926 A s t f)). Qed.
Lemma lem3705928 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term255 A s t f) = (term349 A s t f).
Proof. exact (EQ_MP (@lem3705927 A s t f) (@lem3705912 A s t f)). Qed.
Lemma lem3705929 {A : Type'} (s : A -> Prop) (f : A -> A) : (term276 A s f) = (term350 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3705928 A s t f)). Qed.
Lemma lem3705930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705931 {A : Type'} (s : A -> Prop) (f : A -> A) : (term291 A s f) = (term351 A s f).
Proof. exact (MK_COMB (@lem3705930 A) (@lem3705929 A s f)). Qed.
Lemma lem3705933 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3705934 {A : Type'} (P : type639 A) : (term354 A P) = (term355 A P).
Proof. exact (@lem3705933 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem3705935 {A : Type'} (s : A -> Prop) (f : A -> A) : (term356 A s f) = (term357 A s f).
Proof. exact (@lem3705934 A (term358 A s f)). Qed.
Lemma lem3705936 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term359 A s f t) = (term348 A s t f).
Proof. exact (eq_refl (term359 A s f t)). Qed.
Lemma lem3705937 {A : Type'} (s' : A -> Prop) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3705938 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term360 A s f t s') = (term361 A s t f s').
Proof. exact (MK_COMB (@lem3705936 A s t f) (@lem3705937 A s')). Qed.
Lemma lem3705939 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term361 A s t f s') = (term346 A s t f s').
Proof. exact (eq_refl (term361 A s t f s')). Qed.
Lemma lem3705940 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term360 A s f t s') = (term346 A s t f s').
Proof. exact (TRANS (@lem3705938 A s t f s') (@lem3705939 A s t f s')). Qed.
Lemma lem3705941 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term362 A s f t) = (term348 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3705940 A s t f s')). Qed.
Lemma lem3705942 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3705943 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term363 A s f t) = (term349 A s t f).
Proof. exact (MK_COMB (@lem3705942 A) (@lem3705941 A s t f)). Qed.
Lemma lem3705944 {A : Type'} (s : A -> Prop) (f : A -> A) : (term364 A s f) = (term350 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3705943 A s t f)). Qed.
Lemma lem3705945 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705946 {A : Type'} (s : A -> Prop) (f : A -> A) : (term356 A s f) = (term351 A s f).
Proof. exact (MK_COMB (@lem3705945 A) (@lem3705944 A s f)). Qed.
Lemma lem3705947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3705948 {A : Type'} (s : A -> Prop) (f : A -> A) : (term365 A s f) = (term366 A s f).
Proof. exact (MK_COMB (@lem3705947) (@lem3705946 A s f)). Qed.
Lemma lem3705949 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term359 A s f t) = (term348 A s t f).
Proof. exact (eq_refl (term359 A s f t)). Qed.
Lemma lem3705950 {A : Type'} (s' : type672 A) (t : A -> Prop) : (s' t) = (s' t).
Proof. exact (eq_refl (s' t)). Qed.
Lemma lem3705951 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) (t : A -> Prop) : (term367 A s f s' t) = (term368 A s f s' t).
Proof. exact (MK_COMB (@lem3705949 A s t f) (@lem3705950 A s' t)). Qed.
Lemma lem3705952 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) (t : A -> Prop) : (term368 A s f s' t) = (term369 A s f s' t).
Proof. exact (eq_refl (term368 A s f s' t)). Qed.
Lemma lem3705953 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) (t : A -> Prop) : (term367 A s f s' t) = (term369 A s f s' t).
Proof. exact (TRANS (@lem3705951 A s f s' t) (@lem3705952 A s f s' t)). Qed.
Lemma lem3705954 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term370 A s f s') = (term371 A s f s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3705953 A s f s' t)). Qed.
Lemma lem3705955 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705956 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term372 A s f s') = (term373 A s f s').
Proof. exact (MK_COMB (@lem3705955 A) (@lem3705954 A s f s')). Qed.
Lemma lem3705957 {A : Type'} (s : A -> Prop) (f : A -> A) : (term374 A s f) = (term375 A s f).
Proof. exact (fun_ext (fun s' : type672 A => @lem3705956 A s f s')). Qed.
Lemma lem3705958 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3705959 {A : Type'} (s : A -> Prop) (f : A -> A) : (term357 A s f) = (term376 A s f).
Proof. exact (MK_COMB (@lem3705958 A) (@lem3705957 A s f)). Qed.
Lemma lem3705960 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term356 A s f) = (term357 A s f)) = ((term351 A s f) = (term376 A s f)).
Proof. exact (MK_COMB (@lem3705948 A s f) (@lem3705959 A s f)). Qed.
Lemma lem3705961 {A : Type'} (s : A -> Prop) (f : A -> A) : (term351 A s f) = (term376 A s f).
Proof. exact (EQ_MP (@lem3705960 A s f) (@lem3705935 A s f)). Qed.
Lemma lem3705962 {A : Type'} (s : A -> Prop) (f : A -> A) : (term291 A s f) = (term376 A s f).
Proof. exact (TRANS (@lem3705931 A s f) (@lem3705961 A s f)). Qed.
Lemma lem3705963 {A : Type'} (f : A -> A) : (term298 A f) = (term377 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705962 A s f)). Qed.
Lemma lem3705964 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705965 {A : Type'} (f : A -> A) : (term313 A f) = (term378 A f).
Proof. exact (MK_COMB (@lem3705964 A) (@lem3705963 A f)). Qed.
Lemma lem3705967 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3705968 {A : Type'} (P : type596 A) : (term379 A P) = (term380 A P).
Proof. exact (@lem3705967 (A -> Prop) (type672 A) P). Qed.
Lemma lem3705969 {A : Type'} (f : A -> A) : (term381 A f) = (term382 A f).
Proof. exact (@lem3705968 A (term383 A f)). Qed.
Lemma lem3705970 {A : Type'} (s : A -> Prop) (f : A -> A) : (term384 A f s) = (term375 A s f).
Proof. exact (eq_refl (term384 A f s)). Qed.
Lemma lem3705971 {A : Type'} (s' : type672 A) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3705972 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term385 A f s s') = (term386 A s f s').
Proof. exact (MK_COMB (@lem3705970 A s f) (@lem3705971 A s')). Qed.
Lemma lem3705973 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term386 A s f s') = (term373 A s f s').
Proof. exact (eq_refl (term386 A s f s')). Qed.
Lemma lem3705974 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term385 A f s s') = (term373 A s f s').
Proof. exact (TRANS (@lem3705972 A s f s') (@lem3705973 A s f s')). Qed.
Lemma lem3705975 {A : Type'} (s : A -> Prop) (f : A -> A) : (term387 A f s) = (term375 A s f).
Proof. exact (fun_ext (fun s' : type672 A => @lem3705974 A s f s')). Qed.
Lemma lem3705976 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3705977 {A : Type'} (s : A -> Prop) (f : A -> A) : (term388 A f s) = (term376 A s f).
Proof. exact (MK_COMB (@lem3705976 A) (@lem3705975 A s f)). Qed.
Lemma lem3705978 {A : Type'} (f : A -> A) : (term389 A f) = (term377 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705977 A s f)). Qed.
Lemma lem3705979 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705980 {A : Type'} (f : A -> A) : (term381 A f) = (term378 A f).
Proof. exact (MK_COMB (@lem3705979 A) (@lem3705978 A f)). Qed.
Lemma lem3705981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3705982 {A : Type'} (f : A -> A) : (term390 A f) = (term391 A f).
Proof. exact (MK_COMB (@lem3705981) (@lem3705980 A f)). Qed.
Lemma lem3705983 {A : Type'} (s : A -> Prop) (f : A -> A) : (term384 A f s) = (term375 A s f).
Proof. exact (eq_refl (term384 A f s)). Qed.
Lemma lem3705984 {A : Type'} (s' : type636 A) (s : A -> Prop) : (s' s) = (s' s).
Proof. exact (eq_refl (s' s)). Qed.
Lemma lem3705985 {A : Type'} (f : A -> A) (s' : type636 A) (s : A -> Prop) : (term392 A f s' s) = (term393 A f s' s).
Proof. exact (MK_COMB (@lem3705983 A s f) (@lem3705984 A s' s)). Qed.
Lemma lem3705986 {A : Type'} (f : A -> A) (s' : type636 A) (s : A -> Prop) : (term393 A f s' s) = (term394 A f s' s).
Proof. exact (eq_refl (term393 A f s' s)). Qed.
Lemma lem3705987 {A : Type'} (f : A -> A) (s' : type636 A) (s : A -> Prop) : (term392 A f s' s) = (term394 A f s' s).
Proof. exact (TRANS (@lem3705985 A f s' s) (@lem3705986 A f s' s)). Qed.
Lemma lem3705988 {A : Type'} (f : A -> A) (s' : type636 A) : (term395 A f s') = (term396 A f s').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3705987 A f s' s)). Qed.
Lemma lem3705989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3705990 {A : Type'} (f : A -> A) (s' : type636 A) : (term397 A f s') = (term398 A f s').
Proof. exact (MK_COMB (@lem3705989 A) (@lem3705988 A f s')). Qed.
Lemma lem3705991 {A : Type'} (f : A -> A) : (term399 A f) = (term400 A f).
Proof. exact (fun_ext (fun s' : type636 A => @lem3705990 A f s')). Qed.
Lemma lem3705992 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3705993 {A : Type'} (f : A -> A) : (term382 A f) = (term401 A f).
Proof. exact (MK_COMB (@lem3705992 A) (@lem3705991 A f)). Qed.
Lemma lem3705994 {A : Type'} (f : A -> A) : ((term381 A f) = (term382 A f)) = ((term378 A f) = (term401 A f)).
Proof. exact (MK_COMB (@lem3705982 A f) (@lem3705993 A f)). Qed.
Lemma lem3705995 {A : Type'} (f : A -> A) : (term378 A f) = (term401 A f).
Proof. exact (EQ_MP (@lem3705994 A f) (@lem3705969 A f)). Qed.
Lemma lem3705996 {A : Type'} (f : A -> A) : (term313 A f) = (term401 A f).
Proof. exact (TRANS (@lem3705965 A f) (@lem3705995 A f)). Qed.
Lemma lem3705997 {A : Type'} : (term322 A) = (term402 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3705996 A f)). Qed.
Lemma lem3705998 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3705999 {A : Type'} : (term337 A) = (term403 A).
Proof. exact (MK_COMB (@lem3705998 A) (@lem3705997 A)). Qed.
Lemma lem3706001 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3706002 {A : Type'} (P : type480 A) : (term404 A P) = (term405 A P).
Proof. exact (@lem3706001 (A -> A) (type636 A) P). Qed.
Lemma lem3706003 {A : Type'} : (term406 A) = (term407 A).
Proof. exact (@lem3706002 A (term408 A)). Qed.
Lemma lem3706004 {A : Type'} (f : A -> A) : (term409 A f) = (term400 A f).
Proof. exact (eq_refl (term409 A f)). Qed.
Lemma lem3706005 {A : Type'} (s' : type636 A) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3706006 {A : Type'} (f : A -> A) (s' : type636 A) : (term410 A f s') = (term411 A f s').
Proof. exact (MK_COMB (@lem3706004 A f) (@lem3706005 A s')). Qed.
Lemma lem3706007 {A : Type'} (f : A -> A) (s' : type636 A) : (term411 A f s') = (term398 A f s').
Proof. exact (eq_refl (term411 A f s')). Qed.
Lemma lem3706008 {A : Type'} (f : A -> A) (s' : type636 A) : (term410 A f s') = (term398 A f s').
Proof. exact (TRANS (@lem3706006 A f s') (@lem3706007 A f s')). Qed.
Lemma lem3706009 {A : Type'} (f : A -> A) : (term412 A f) = (term400 A f).
Proof. exact (fun_ext (fun s' : type636 A => @lem3706008 A f s')). Qed.
Lemma lem3706010 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3706011 {A : Type'} (f : A -> A) : (term413 A f) = (term401 A f).
Proof. exact (MK_COMB (@lem3706010 A) (@lem3706009 A f)). Qed.
Lemma lem3706012 {A : Type'} : (term414 A) = (term402 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3706011 A f)). Qed.
Lemma lem3706013 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3706014 {A : Type'} : (term406 A) = (term403 A).
Proof. exact (MK_COMB (@lem3706013 A) (@lem3706012 A)). Qed.
Lemma lem3706015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706016 {A : Type'} : (term415 A) = (term416 A).
Proof. exact (MK_COMB (@lem3706015) (@lem3706014 A)). Qed.
Lemma lem3706017 {A : Type'} (f : A -> A) : (term409 A f) = (term400 A f).
Proof. exact (eq_refl (term409 A f)). Qed.
Lemma lem3706018 {A : Type'} (s' : type483 A) (f : A -> A) : (s' f) = (s' f).
Proof. exact (eq_refl (s' f)). Qed.
Lemma lem3706019 {A : Type'} (s' : type483 A) (f : A -> A) : (term417 A s' f) = (term418 A s' f).
Proof. exact (MK_COMB (@lem3706017 A f) (@lem3706018 A s' f)). Qed.
Lemma lem3706020 {A : Type'} (s' : type483 A) (f : A -> A) : (term418 A s' f) = (term419 A s' f).
Proof. exact (eq_refl (term418 A s' f)). Qed.
Lemma lem3706021 {A : Type'} (s' : type483 A) (f : A -> A) : (term417 A s' f) = (term419 A s' f).
Proof. exact (TRANS (@lem3706019 A s' f) (@lem3706020 A s' f)). Qed.
Lemma lem3706022 {A : Type'} (s' : type483 A) : (term420 A s') = (term421 A s').
Proof. exact (fun_ext (fun f : A -> A => @lem3706021 A s' f)). Qed.
Lemma lem3706023 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3706024 {A : Type'} (s' : type483 A) : (term422 A s') = (term423 A s').
Proof. exact (MK_COMB (@lem3706023 A) (@lem3706022 A s')). Qed.
Lemma lem3706025 {A : Type'} : (term424 A) = (term425 A).
Proof. exact (fun_ext (fun s' : type483 A => @lem3706024 A s')). Qed.
Lemma lem3706026 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3706027 {A : Type'} : (term407 A) = (term426 A).
Proof. exact (MK_COMB (@lem3706026 A) (@lem3706025 A)). Qed.
Lemma lem3706028 {A : Type'} : ((term406 A) = (term407 A)) = ((term403 A) = (term426 A)).
Proof. exact (MK_COMB (@lem3706016 A) (@lem3706027 A)). Qed.
Lemma lem3706029 {A : Type'} : (term403 A) = (term426 A).
Proof. exact (EQ_MP (@lem3706028 A) (@lem3706003 A)). Qed.
Lemma lem3706030 {A : Type'} : (term337 A) = (term426 A).
Proof. exact (TRANS (@lem3705999 A) (@lem3706029 A)). Qed.
Lemma lem3706031 {A : Type'} : (term334 A) = (term334 A).
Proof. exact (eq_refl (term334 A)). Qed.
Lemma lem3706032 {A : Type'} : (term338 A) = (term427 A).
Proof. exact (MK_COMB (@lem3706031 A) (@lem3706030 A)). Qed.
Lemma lem3706034 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3706035 {A : Type'} (P : Prop) (Q : type92 A) : (term428 A P Q) = (term429 A P Q).
Proof. exact (@lem3706034 (type483 A) P Q). Qed.
Lemma lem3706036 {A : Type'} : (term430 A) = (term431 A).
Proof. exact (@lem3706035 A (term332 A) (term425 A)). Qed.
Lemma lem3706037 {A : Type'} (s' : type483 A) : (term432 A s') = (term423 A s').
Proof. exact (eq_refl (term432 A s')). Qed.
Lemma lem3706038 {A : Type'} : (term433 A) = (term425 A).
Proof. exact (fun_ext (fun s' : type483 A => @lem3706037 A s')). Qed.
Lemma lem3706039 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3706040 {A : Type'} : (term434 A) = (term426 A).
Proof. exact (MK_COMB (@lem3706039 A) (@lem3706038 A)). Qed.
Lemma lem3706041 {A : Type'} : (term334 A) = (term334 A).
Proof. exact (eq_refl (term334 A)). Qed.
Lemma lem3706042 {A : Type'} : (term430 A) = (term427 A).
Proof. exact (MK_COMB (@lem3706041 A) (@lem3706040 A)). Qed.
Lemma lem3706043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706044 {A : Type'} : (term435 A) = (term436 A).
Proof. exact (MK_COMB (@lem3706043) (@lem3706042 A)). Qed.
Lemma lem3706045 {A : Type'} (s' : type483 A) : (term432 A s') = (term423 A s').
Proof. exact (eq_refl (term432 A s')). Qed.
Lemma lem3706046 {A : Type'} : (term334 A) = (term334 A).
Proof. exact (eq_refl (term334 A)). Qed.
Lemma lem3706047 {A : Type'} (s' : type483 A) : (term437 A s') = (term438 A s').
Proof. exact (MK_COMB (@lem3706046 A) (@lem3706045 A s')). Qed.
Lemma lem3706048 {A : Type'} : (term439 A) = (term440 A).
Proof. exact (fun_ext (fun s' : type483 A => @lem3706047 A s')). Qed.
Lemma lem3706049 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3706050 {A : Type'} : (term431 A) = (term441 A).
Proof. exact (MK_COMB (@lem3706049 A) (@lem3706048 A)). Qed.
Lemma lem3706051 {A : Type'} : ((term430 A) = (term431 A)) = ((term427 A) = (term441 A)).
Proof. exact (MK_COMB (@lem3706044 A) (@lem3706050 A)). Qed.
Lemma lem3706052 {A : Type'} : (term427 A) = (term441 A).
Proof. exact (EQ_MP (@lem3706051 A) (@lem3706036 A)). Qed.
Lemma lem3706053 {A : Type'} : (term338 A) = (term441 A).
Proof. exact (TRANS (@lem3706032 A) (@lem3706052 A)). Qed.
Lemma lem3706054 {A : Type'} : (term268 A) = (term441 A).
Proof. exact (TRANS (@lem3705908 A) (@lem3706053 A)). Qed.
Lemma lem3706055 {A : Type'} : (term12 A) = (term441 A).
Proof. exact (TRANS (@lem3705271 A) (@lem3706054 A)). Qed.
Lemma lem3706056 {A : Type'} (h1 : term12 A) : term441 A.
Proof. exact (EQ_MP (@lem3706055 A) (@lem3704370 A h1)). Qed.
Lemma lem3706065 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term442 A B t f s) = (term443 A B t f s).
Proof. exact (@lem17045 (@FINITE B t) (term444 A B t f s)). Qed.
Lemma lem3706079 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term445 A B s t f s') = (term446 A B s t f s').
Proof. exact (@lem17045 (@SUBSET A s' s) (t = (@IMAGE A B f s'))). Qed.
Lemma lem3706084 {A : Type'} (s' : A -> Prop) : (term82 A s') = (term82 A s').
Proof. exact (eq_refl (term82 A s')). Qed.
Lemma lem3706085 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term447 A B s t f s') = (term448 A B s t f s').
Proof. exact (MK_COMB (@lem3706084 A s') (@lem3706079 A B s t f s')). Qed.
Lemma lem3706086 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term449 A B s t f s') = (term447 A B s t f s').
Proof. exact (@lem17045 (@FINITE A s') (term450 A B s t f s')). Qed.
Lemma lem3706087 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term449 A B s t f s') = (term448 A B s t f s').
Proof. exact (TRANS (@lem3706086 A B s t f s') (@lem3706085 A B s t f s')). Qed.
Lemma lem3706090 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term53 A B s t f s') = (term53 A B s t f s').
Proof. exact (eq_refl (term53 A B s t f s')). Qed.
Lemma lem3706091 {A : Type'} (P : type686 A) : (term87 A P) = (term88 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3706092 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term451 A B s t f) = (term452 A B s t f).
Proof. exact (@lem3706091 A (term54 A B s t f)). Qed.
Lemma lem3706093 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term453 A B s t f s') = (term53 A B s t f s').
Proof. exact (eq_refl (term453 A B s t f s')). Qed.
Lemma lem3706094 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3706095 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term454 A B s t f s') = (term449 A B s t f s').
Proof. exact (MK_COMB (@lem3706094) (@lem3706093 A B s t f s')). Qed.
Lemma lem3706096 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term454 A B s t f s') = (term448 A B s t f s').
Proof. exact (TRANS (@lem3706095 A B s t f s') (@lem3706087 A B s t f s')). Qed.
Lemma lem3706097 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term455 A B s t f) = (term456 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3706096 A B s t f s')). Qed.
Lemma lem3706098 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706099 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term452 A B s t f) = (term457 A B s t f).
Proof. exact (MK_COMB (@lem3706098 A) (@lem3706097 A B s t f)). Qed.
Lemma lem3706100 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term451 A B s t f) = (term457 A B s t f).
Proof. exact (TRANS (@lem3706092 A B s t f) (@lem3706099 A B s t f)). Qed.
Lemma lem3706101 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term54 A B s t f) = (term54 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3706090 A B s t f s')). Qed.
Lemma lem3706102 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3706103 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term55 A B s t f) = (term55 A B s t f).
Proof. exact (MK_COMB (@lem3706102 A) (@lem3706101 A B s t f)). Qed.
Lemma lem3706104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3706105 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term458 A B t f s) = (term459 A B t f s).
Proof. exact (MK_COMB (@lem3706104) (@lem3706065 A B t f s)). Qed.
Lemma lem3706106 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term460 A B s t f) = (term461 A B s t f).
Proof. exact (MK_COMB (@lem3706105 A B t f s) (@lem3706103 A B s t f)). Qed.
Lemma lem3706108 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term462 A B t f s) = (term462 A B t f s).
Proof. exact (eq_refl (term462 A B t f s)). Qed.
Lemma lem3706109 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term463 A B s t f) = (term464 A B s t f).
Proof. exact (MK_COMB (@lem3706108 A B t f s) (@lem3706100 A B s t f)). Qed.
Lemma lem3706110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706111 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term465 A B s t f) = (term466 A B s t f).
Proof. exact (MK_COMB (@lem3706110) (@lem3706109 A B s t f)). Qed.
Lemma lem3706112 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term467 A B s t f) = (term468 A B s t f).
Proof. exact (MK_COMB (@lem3706111 A B s t f) (@lem3706106 A B s t f)). Qed.
Lemma lem3706113 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term57 A B t f s) = (term55 A B s t f)) = (term467 A B s t f).
Proof. exact (@lem17784 (term57 A B t f s) (term55 A B s t f)). Qed.
Lemma lem3706114 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term57 A B t f s) = (term55 A B s t f)) = (term468 A B s t f).
Proof. exact (TRANS (@lem3706113 A B s t f) (@lem3706112 A B s t f)). Qed.
Lemma lem3706115 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term58 A B s f) = (term469 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706114 A B s t f)). Qed.
Lemma lem3706116 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706117 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term470 A B s f).
Proof. exact (MK_COMB (@lem3706116 B) (@lem3706115 A B s f)). Qed.
Lemma lem3706118 {A B : Type'} (f : A -> B) : (term60 A B f) = (term471 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706117 A B s f)). Qed.
Lemma lem3706119 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706120 {A B : Type'} (f : A -> B) : (term61 A B f) = (term472 A B f).
Proof. exact (MK_COMB (@lem3706119 A) (@lem3706118 A B f)). Qed.
Lemma lem3706121 {A B : Type'} : (term62 A B) = (term473 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3706120 A B f)). Qed.
Lemma lem3706122 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706123 {A B : Type'} : (term11 A B) = (term474 A B).
Proof. exact (MK_COMB (@lem3706122 A B) (@lem3706121 A B)). Qed.
Lemma lem3706133 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3706134 {B : Type'} (P : type686 B) (Q : type686 B) : (term271 B P Q) = (term272 B P Q).
Proof. exact (@lem3706133 (B -> Prop) P Q). Qed.
Lemma lem3706135 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term475 A B s f) = (term476 A B s f).
Proof. exact (@lem3706134 B (term477 A B s f) (term478 A B s f)). Qed.
Lemma lem3706136 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term479 A B s f t) = (term464 A B s t f).
Proof. exact (eq_refl (term479 A B s f t)). Qed.
Lemma lem3706137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706138 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term480 A B s f t) = (term466 A B s t f).
Proof. exact (MK_COMB (@lem3706137) (@lem3706136 A B s t f)). Qed.
Lemma lem3706139 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term481 A B s f t) = (term461 A B s t f).
Proof. exact (eq_refl (term481 A B s f t)). Qed.
Lemma lem3706140 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term482 A B s f t) = (term468 A B s t f).
Proof. exact (MK_COMB (@lem3706138 A B s t f) (@lem3706139 A B s t f)). Qed.
Lemma lem3706141 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term483 A B s f) = (term469 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706140 A B s t f)). Qed.
Lemma lem3706142 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706143 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term475 A B s f) = (term470 A B s f).
Proof. exact (MK_COMB (@lem3706142 B) (@lem3706141 A B s f)). Qed.
Lemma lem3706144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706145 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term484 A B s f) = (term485 A B s f).
Proof. exact (MK_COMB (@lem3706144) (@lem3706143 A B s f)). Qed.
Lemma lem3706146 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term479 A B s f t) = (term464 A B s t f).
Proof. exact (eq_refl (term479 A B s f t)). Qed.
Lemma lem3706147 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term486 A B s f) = (term477 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706146 A B s t f)). Qed.
Lemma lem3706148 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706149 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term487 A B s f) = (term488 A B s f).
Proof. exact (MK_COMB (@lem3706148 B) (@lem3706147 A B s f)). Qed.
Lemma lem3706150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706151 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term489 A B s f) = (term490 A B s f).
Proof. exact (MK_COMB (@lem3706150) (@lem3706149 A B s f)). Qed.
Lemma lem3706152 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term481 A B s f t) = (term461 A B s t f).
Proof. exact (eq_refl (term481 A B s f t)). Qed.
Lemma lem3706153 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term491 A B s f) = (term478 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706152 A B s t f)). Qed.
Lemma lem3706154 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706155 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term492 A B s f) = (term493 A B s f).
Proof. exact (MK_COMB (@lem3706154 B) (@lem3706153 A B s f)). Qed.
Lemma lem3706156 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term476 A B s f) = (term494 A B s f).
Proof. exact (MK_COMB (@lem3706151 A B s f) (@lem3706155 A B s f)). Qed.
Lemma lem3706157 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term475 A B s f) = (term476 A B s f)) = ((term470 A B s f) = (term494 A B s f)).
Proof. exact (MK_COMB (@lem3706145 A B s f) (@lem3706156 A B s f)). Qed.
Lemma lem3706158 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term470 A B s f) = (term494 A B s f).
Proof. exact (EQ_MP (@lem3706157 A B s f) (@lem3706135 A B s f)). Qed.
Lemma lem3706331 {A B : Type'} (f : A -> B) : (term471 A B f) = (term495 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706158 A B s f)). Qed.
Lemma lem3706332 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706333 {A B : Type'} (f : A -> B) : (term472 A B f) = (term496 A B f).
Proof. exact (MK_COMB (@lem3706332 A) (@lem3706331 A B f)). Qed.
Lemma lem3706335 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3706336 {A : Type'} (P : type686 A) (Q : type686 A) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem3706335 (A -> Prop) P Q). Qed.
Lemma lem3706337 {A B : Type'} (f : A -> B) : (term497 A B f) = (term498 A B f).
Proof. exact (@lem3706336 A (term499 A B f) (term500 A B f)). Qed.
Lemma lem3706338 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term501 A B f s) = (term488 A B s f).
Proof. exact (eq_refl (term501 A B f s)). Qed.
Lemma lem3706339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706340 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term502 A B f s) = (term490 A B s f).
Proof. exact (MK_COMB (@lem3706339) (@lem3706338 A B s f)). Qed.
Lemma lem3706341 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term503 A B f s) = (term493 A B s f).
Proof. exact (eq_refl (term503 A B f s)). Qed.
Lemma lem3706342 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term504 A B f s) = (term494 A B s f).
Proof. exact (MK_COMB (@lem3706340 A B s f) (@lem3706341 A B s f)). Qed.
Lemma lem3706343 {A B : Type'} (f : A -> B) : (term505 A B f) = (term495 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706342 A B s f)). Qed.
Lemma lem3706344 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706345 {A B : Type'} (f : A -> B) : (term497 A B f) = (term496 A B f).
Proof. exact (MK_COMB (@lem3706344 A) (@lem3706343 A B f)). Qed.
Lemma lem3706346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706347 {A B : Type'} (f : A -> B) : (term506 A B f) = (term507 A B f).
Proof. exact (MK_COMB (@lem3706346) (@lem3706345 A B f)). Qed.
Lemma lem3706348 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term501 A B f s) = (term488 A B s f).
Proof. exact (eq_refl (term501 A B f s)). Qed.
Lemma lem3706349 {A B : Type'} (f : A -> B) : (term508 A B f) = (term499 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706348 A B s f)). Qed.
Lemma lem3706350 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706351 {A B : Type'} (f : A -> B) : (term509 A B f) = (term510 A B f).
Proof. exact (MK_COMB (@lem3706350 A) (@lem3706349 A B f)). Qed.
Lemma lem3706352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706353 {A B : Type'} (f : A -> B) : (term511 A B f) = (term512 A B f).
Proof. exact (MK_COMB (@lem3706352) (@lem3706351 A B f)). Qed.
Lemma lem3706354 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term503 A B f s) = (term493 A B s f).
Proof. exact (eq_refl (term503 A B f s)). Qed.
Lemma lem3706355 {A B : Type'} (f : A -> B) : (term513 A B f) = (term500 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706354 A B s f)). Qed.
Lemma lem3706356 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706357 {A B : Type'} (f : A -> B) : (term514 A B f) = (term515 A B f).
Proof. exact (MK_COMB (@lem3706356 A) (@lem3706355 A B f)). Qed.
Lemma lem3706358 {A B : Type'} (f : A -> B) : (term498 A B f) = (term516 A B f).
Proof. exact (MK_COMB (@lem3706353 A B f) (@lem3706357 A B f)). Qed.
Lemma lem3706359 {A B : Type'} (f : A -> B) : ((term497 A B f) = (term498 A B f)) = ((term496 A B f) = (term516 A B f)).
Proof. exact (MK_COMB (@lem3706347 A B f) (@lem3706358 A B f)). Qed.
Lemma lem3706360 {A B : Type'} (f : A -> B) : (term496 A B f) = (term516 A B f).
Proof. exact (EQ_MP (@lem3706359 A B f) (@lem3706337 A B f)). Qed.
Lemma lem3706541 {A B : Type'} (f : A -> B) : (term472 A B f) = (term516 A B f).
Proof. exact (TRANS (@lem3706333 A B f) (@lem3706360 A B f)). Qed.
Lemma lem3706542 {A B : Type'} : (term473 A B) = (term517 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3706541 A B f)). Qed.
Lemma lem3706543 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706544 {A B : Type'} : (term474 A B) = (term518 A B).
Proof. exact (MK_COMB (@lem3706543 A B) (@lem3706542 A B)). Qed.
Lemma lem3706546 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3706547 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term519 A B P Q) = (term520 A B P Q).
Proof. exact (@lem3706546 (A -> B) P Q). Qed.
Lemma lem3706548 {A B : Type'} : (term521 A B) = (term522 A B).
Proof. exact (@lem3706547 A B (term523 A B) (term524 A B)). Qed.
Lemma lem3706549 {A B : Type'} (f : A -> B) : (term525 A B f) = (term510 A B f).
Proof. exact (eq_refl (term525 A B f)). Qed.
Lemma lem3706550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706551 {A B : Type'} (f : A -> B) : (term526 A B f) = (term512 A B f).
Proof. exact (MK_COMB (@lem3706550) (@lem3706549 A B f)). Qed.
Lemma lem3706552 {A B : Type'} (f : A -> B) : (term527 A B f) = (term515 A B f).
Proof. exact (eq_refl (term527 A B f)). Qed.
Lemma lem3706553 {A B : Type'} (f : A -> B) : (term528 A B f) = (term516 A B f).
Proof. exact (MK_COMB (@lem3706551 A B f) (@lem3706552 A B f)). Qed.
Lemma lem3706554 {A B : Type'} : (term529 A B) = (term517 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3706553 A B f)). Qed.
Lemma lem3706555 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706556 {A B : Type'} : (term521 A B) = (term518 A B).
Proof. exact (MK_COMB (@lem3706555 A B) (@lem3706554 A B)). Qed.
Lemma lem3706557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706558 {A B : Type'} : (term530 A B) = (term531 A B).
Proof. exact (MK_COMB (@lem3706557) (@lem3706556 A B)). Qed.
Lemma lem3706559 {A B : Type'} (f : A -> B) : (term525 A B f) = (term510 A B f).
Proof. exact (eq_refl (term525 A B f)). Qed.
Lemma lem3706560 {A B : Type'} : (term532 A B) = (term523 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3706559 A B f)). Qed.
Lemma lem3706561 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706562 {A B : Type'} : (term533 A B) = (term534 A B).
Proof. exact (MK_COMB (@lem3706561 A B) (@lem3706560 A B)). Qed.
Lemma lem3706563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706564 {A B : Type'} : (term535 A B) = (term536 A B).
Proof. exact (MK_COMB (@lem3706563) (@lem3706562 A B)). Qed.
Lemma lem3706565 {A B : Type'} (f : A -> B) : (term527 A B f) = (term515 A B f).
Proof. exact (eq_refl (term527 A B f)). Qed.
Lemma lem3706566 {A B : Type'} : (term537 A B) = (term524 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3706565 A B f)). Qed.
Lemma lem3706567 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706568 {A B : Type'} : (term538 A B) = (term539 A B).
Proof. exact (MK_COMB (@lem3706567 A B) (@lem3706566 A B)). Qed.
Lemma lem3706569 {A B : Type'} : (term522 A B) = (term540 A B).
Proof. exact (MK_COMB (@lem3706564 A B) (@lem3706568 A B)). Qed.
Lemma lem3706570 {A B : Type'} : ((term521 A B) = (term522 A B)) = ((term518 A B) = (term540 A B)).
Proof. exact (MK_COMB (@lem3706558 A B) (@lem3706569 A B)). Qed.
Lemma lem3706571 {A B : Type'} : (term518 A B) = (term540 A B).
Proof. exact (EQ_MP (@lem3706570 A B) (@lem3706548 A B)). Qed.
Lemma lem3706760 {A B : Type'} : (term474 A B) = (term540 A B).
Proof. exact (TRANS (@lem3706544 A B) (@lem3706571 A B)). Qed.
Lemma lem3706762 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3706763 {A : Type'} (P : Prop) (Q : type686 A) : (term218 A P Q) = (term219 A P Q).
Proof. exact (@lem3706762 (A -> Prop) P Q). Qed.
Lemma lem3706764 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term541 A B s t f) = (term542 A B s t f).
Proof. exact (@lem3706763 A (term443 A B t f s) (term54 A B s t f)). Qed.
Lemma lem3706765 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term453 A B s t f s') = (term53 A B s t f s').
Proof. exact (eq_refl (term453 A B s t f s')). Qed.
Lemma lem3706766 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term543 A B s t f) = (term54 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3706765 A B s t f s')). Qed.
Lemma lem3706767 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3706768 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term544 A B s t f) = (term55 A B s t f).
Proof. exact (MK_COMB (@lem3706767 A) (@lem3706766 A B s t f)). Qed.
Lemma lem3706769 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term459 A B t f s) = (term459 A B t f s).
Proof. exact (eq_refl (term459 A B t f s)). Qed.
Lemma lem3706770 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term541 A B s t f) = (term461 A B s t f).
Proof. exact (MK_COMB (@lem3706769 A B t f s) (@lem3706768 A B s t f)). Qed.
Lemma lem3706771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706772 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term545 A B s t f) = (term546 A B s t f).
Proof. exact (MK_COMB (@lem3706771) (@lem3706770 A B s t f)). Qed.
Lemma lem3706773 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term453 A B s t f s') = (term53 A B s t f s').
Proof. exact (eq_refl (term453 A B s t f s')). Qed.
Lemma lem3706774 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term459 A B t f s) = (term459 A B t f s).
Proof. exact (eq_refl (term459 A B t f s)). Qed.
Lemma lem3706775 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term547 A B s t f s') = (term548 A B s t f s').
Proof. exact (MK_COMB (@lem3706774 A B t f s) (@lem3706773 A B s t f s')). Qed.
Lemma lem3706776 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term549 A B s t f) = (term550 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3706775 A B s t f s')). Qed.
Lemma lem3706777 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3706778 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term542 A B s t f) = (term551 A B s t f).
Proof. exact (MK_COMB (@lem3706777 A) (@lem3706776 A B s t f)). Qed.
Lemma lem3706779 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term541 A B s t f) = (term542 A B s t f)) = ((term461 A B s t f) = (term551 A B s t f)).
Proof. exact (MK_COMB (@lem3706772 A B s t f) (@lem3706778 A B s t f)). Qed.
Lemma lem3706780 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term461 A B s t f) = (term551 A B s t f).
Proof. exact (EQ_MP (@lem3706779 A B s t f) (@lem3706764 A B s t f)). Qed.
Lemma lem3706781 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term478 A B s f) = (term552 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706780 A B s t f)). Qed.
Lemma lem3706782 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706783 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term493 A B s f) = (term553 A B s f).
Proof. exact (MK_COMB (@lem3706782 B) (@lem3706781 A B s f)). Qed.
Lemma lem3706785 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3706786 {A B : Type'} (P : type841 A B) : (term554 A B P) = (term555 A B P).
Proof. exact (@lem3706785 (B -> Prop) (A -> Prop) P). Qed.
Lemma lem3706787 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term556 A B s f) = (term557 A B s f).
Proof. exact (@lem3706786 A B (term558 A B s f)). Qed.
Lemma lem3706788 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term559 A B s f t) = (term550 A B s t f).
Proof. exact (eq_refl (term559 A B s f t)). Qed.
Lemma lem3706789 {A : Type'} (s' : A -> Prop) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3706790 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term560 A B s f t s') = (term561 A B s t f s').
Proof. exact (MK_COMB (@lem3706788 A B s t f) (@lem3706789 A s')). Qed.
Lemma lem3706791 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term561 A B s t f s') = (term548 A B s t f s').
Proof. exact (eq_refl (term561 A B s t f s')). Qed.
Lemma lem3706792 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term560 A B s f t s') = (term548 A B s t f s').
Proof. exact (TRANS (@lem3706790 A B s t f s') (@lem3706791 A B s t f s')). Qed.
Lemma lem3706793 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term562 A B s f t) = (term550 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3706792 A B s t f s')). Qed.
Lemma lem3706794 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3706795 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term563 A B s f t) = (term551 A B s t f).
Proof. exact (MK_COMB (@lem3706794 A) (@lem3706793 A B s t f)). Qed.
Lemma lem3706796 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term564 A B s f) = (term552 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706795 A B s t f)). Qed.
Lemma lem3706797 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706798 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term556 A B s f) = (term553 A B s f).
Proof. exact (MK_COMB (@lem3706797 B) (@lem3706796 A B s f)). Qed.
Lemma lem3706799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706800 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term565 A B s f) = (term566 A B s f).
Proof. exact (MK_COMB (@lem3706799) (@lem3706798 A B s f)). Qed.
Lemma lem3706801 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term559 A B s f t) = (term550 A B s t f).
Proof. exact (eq_refl (term559 A B s f t)). Qed.
Lemma lem3706802 {A B : Type'} (s' : type860 A B) (t : B -> Prop) : (s' t) = (s' t).
Proof. exact (eq_refl (s' t)). Qed.
Lemma lem3706803 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) (t : B -> Prop) : (term567 A B s f s' t) = (term568 A B s f s' t).
Proof. exact (MK_COMB (@lem3706801 A B s t f) (@lem3706802 A B s' t)). Qed.
Lemma lem3706804 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) (t : B -> Prop) : (term568 A B s f s' t) = (term569 A B s f s' t).
Proof. exact (eq_refl (term568 A B s f s' t)). Qed.
Lemma lem3706805 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) (t : B -> Prop) : (term567 A B s f s' t) = (term569 A B s f s' t).
Proof. exact (TRANS (@lem3706803 A B s f s' t) (@lem3706804 A B s f s' t)). Qed.
Lemma lem3706806 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term570 A B s f s') = (term571 A B s f s').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706805 A B s f s' t)). Qed.
Lemma lem3706807 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706808 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term572 A B s f s') = (term573 A B s f s').
Proof. exact (MK_COMB (@lem3706807 B) (@lem3706806 A B s f s')). Qed.
Lemma lem3706809 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term574 A B s f) = (term575 A B s f).
Proof. exact (fun_ext (fun s' : type860 A B => @lem3706808 A B s f s')). Qed.
Lemma lem3706810 {A B : Type'} : (@ex ((B -> Prop) -> A -> Prop)) = (@ex ((B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> A -> Prop))). Qed.
Lemma lem3706811 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term557 A B s f) = (term576 A B s f).
Proof. exact (MK_COMB (@lem3706810 A B) (@lem3706809 A B s f)). Qed.
Lemma lem3706812 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term556 A B s f) = (term557 A B s f)) = ((term553 A B s f) = (term576 A B s f)).
Proof. exact (MK_COMB (@lem3706800 A B s f) (@lem3706811 A B s f)). Qed.
Lemma lem3706813 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term553 A B s f) = (term576 A B s f).
Proof. exact (EQ_MP (@lem3706812 A B s f) (@lem3706787 A B s f)). Qed.
Lemma lem3706814 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term493 A B s f) = (term576 A B s f).
Proof. exact (TRANS (@lem3706783 A B s f) (@lem3706813 A B s f)). Qed.
Lemma lem3706815 {A B : Type'} (f : A -> B) : (term500 A B f) = (term577 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706814 A B s f)). Qed.
Lemma lem3706816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706817 {A B : Type'} (f : A -> B) : (term515 A B f) = (term578 A B f).
Proof. exact (MK_COMB (@lem3706816 A) (@lem3706815 A B f)). Qed.
Lemma lem3706819 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3706820 {A B : Type'} (P : type607 A B) : (term579 A B P) = (term580 A B P).
Proof. exact (@lem3706819 (A -> Prop) (type860 A B) P). Qed.
Lemma lem3706821 {A B : Type'} (f : A -> B) : (term581 A B f) = (term582 A B f).
Proof. exact (@lem3706820 A B (term583 A B f)). Qed.
Lemma lem3706822 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term584 A B f s) = (term575 A B s f).
Proof. exact (eq_refl (term584 A B f s)). Qed.
Lemma lem3706823 {A B : Type'} (s' : type860 A B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3706824 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term585 A B f s s') = (term586 A B s f s').
Proof. exact (MK_COMB (@lem3706822 A B s f) (@lem3706823 A B s')). Qed.
Lemma lem3706825 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term586 A B s f s') = (term573 A B s f s').
Proof. exact (eq_refl (term586 A B s f s')). Qed.
Lemma lem3706826 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term585 A B f s s') = (term573 A B s f s').
Proof. exact (TRANS (@lem3706824 A B s f s') (@lem3706825 A B s f s')). Qed.
Lemma lem3706827 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term587 A B f s) = (term575 A B s f).
Proof. exact (fun_ext (fun s' : type860 A B => @lem3706826 A B s f s')). Qed.
Lemma lem3706828 {A B : Type'} : (@ex ((B -> Prop) -> A -> Prop)) = (@ex ((B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> A -> Prop))). Qed.
Lemma lem3706829 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term588 A B f s) = (term576 A B s f).
Proof. exact (MK_COMB (@lem3706828 A B) (@lem3706827 A B s f)). Qed.
Lemma lem3706830 {A B : Type'} (f : A -> B) : (term589 A B f) = (term577 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706829 A B s f)). Qed.
Lemma lem3706831 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706832 {A B : Type'} (f : A -> B) : (term581 A B f) = (term578 A B f).
Proof. exact (MK_COMB (@lem3706831 A) (@lem3706830 A B f)). Qed.
Lemma lem3706833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706834 {A B : Type'} (f : A -> B) : (term590 A B f) = (term591 A B f).
Proof. exact (MK_COMB (@lem3706833) (@lem3706832 A B f)). Qed.
Lemma lem3706835 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term584 A B f s) = (term575 A B s f).
Proof. exact (eq_refl (term584 A B f s)). Qed.
Lemma lem3706836 {A B : Type'} (s' : type657 A B) (s : A -> Prop) : (s' s) = (s' s).
Proof. exact (eq_refl (s' s)). Qed.
Lemma lem3706837 {A B : Type'} (f : A -> B) (s' : type657 A B) (s : A -> Prop) : (term592 A B f s' s) = (term593 A B f s' s).
Proof. exact (MK_COMB (@lem3706835 A B s f) (@lem3706836 A B s' s)). Qed.
Lemma lem3706838 {A B : Type'} (f : A -> B) (s' : type657 A B) (s : A -> Prop) : (term593 A B f s' s) = (term594 A B f s' s).
Proof. exact (eq_refl (term593 A B f s' s)). Qed.
Lemma lem3706839 {A B : Type'} (f : A -> B) (s' : type657 A B) (s : A -> Prop) : (term592 A B f s' s) = (term594 A B f s' s).
Proof. exact (TRANS (@lem3706837 A B f s' s) (@lem3706838 A B f s' s)). Qed.
Lemma lem3706840 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term595 A B f s') = (term596 A B f s').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3706839 A B f s' s)). Qed.
Lemma lem3706841 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3706842 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term597 A B f s') = (term598 A B f s').
Proof. exact (MK_COMB (@lem3706841 A) (@lem3706840 A B f s')). Qed.
Lemma lem3706843 {A B : Type'} (f : A -> B) : (term599 A B f) = (term600 A B f).
Proof. exact (fun_ext (fun s' : type657 A B => @lem3706842 A B f s')). Qed.
Lemma lem3706844 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3706845 {A B : Type'} (f : A -> B) : (term582 A B f) = (term601 A B f).
Proof. exact (MK_COMB (@lem3706844 A B) (@lem3706843 A B f)). Qed.
Lemma lem3706846 {A B : Type'} (f : A -> B) : ((term581 A B f) = (term582 A B f)) = ((term578 A B f) = (term601 A B f)).
Proof. exact (MK_COMB (@lem3706834 A B f) (@lem3706845 A B f)). Qed.
Lemma lem3706847 {A B : Type'} (f : A -> B) : (term578 A B f) = (term601 A B f).
Proof. exact (EQ_MP (@lem3706846 A B f) (@lem3706821 A B f)). Qed.
Lemma lem3706848 {A B : Type'} (f : A -> B) : (term515 A B f) = (term601 A B f).
Proof. exact (TRANS (@lem3706817 A B f) (@lem3706847 A B f)). Qed.
Lemma lem3706849 {A B : Type'} : (term524 A B) = (term602 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3706848 A B f)). Qed.
Lemma lem3706850 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706851 {A B : Type'} : (term539 A B) = (term603 A B).
Proof. exact (MK_COMB (@lem3706850 A B) (@lem3706849 A B)). Qed.
Lemma lem3706853 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3706854 {A B : Type'} (P : type501 A B) : (term604 A B P) = (term605 A B P).
Proof. exact (@lem3706853 (A -> B) (type657 A B) P). Qed.
Lemma lem3706855 {A B : Type'} : (term606 A B) = (term607 A B).
Proof. exact (@lem3706854 A B (term608 A B)). Qed.
Lemma lem3706856 {A B : Type'} (f : A -> B) : (term609 A B f) = (term600 A B f).
Proof. exact (eq_refl (term609 A B f)). Qed.
Lemma lem3706857 {A B : Type'} (s' : type657 A B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3706858 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term610 A B f s') = (term611 A B f s').
Proof. exact (MK_COMB (@lem3706856 A B f) (@lem3706857 A B s')). Qed.
Lemma lem3706859 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term611 A B f s') = (term598 A B f s').
Proof. exact (eq_refl (term611 A B f s')). Qed.
Lemma lem3706860 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term610 A B f s') = (term598 A B f s').
Proof. exact (TRANS (@lem3706858 A B f s') (@lem3706859 A B f s')). Qed.
Lemma lem3706861 {A B : Type'} (f : A -> B) : (term612 A B f) = (term600 A B f).
Proof. exact (fun_ext (fun s' : type657 A B => @lem3706860 A B f s')). Qed.
Lemma lem3706862 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3706863 {A B : Type'} (f : A -> B) : (term613 A B f) = (term601 A B f).
Proof. exact (MK_COMB (@lem3706862 A B) (@lem3706861 A B f)). Qed.
Lemma lem3706864 {A B : Type'} : (term614 A B) = (term602 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3706863 A B f)). Qed.
Lemma lem3706865 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706866 {A B : Type'} : (term606 A B) = (term603 A B).
Proof. exact (MK_COMB (@lem3706865 A B) (@lem3706864 A B)). Qed.
Lemma lem3706867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706868 {A B : Type'} : (term615 A B) = (term616 A B).
Proof. exact (MK_COMB (@lem3706867) (@lem3706866 A B)). Qed.
Lemma lem3706869 {A B : Type'} (f : A -> B) : (term609 A B f) = (term600 A B f).
Proof. exact (eq_refl (term609 A B f)). Qed.
Lemma lem3706870 {A B : Type'} (s' : type525 A B) (f : A -> B) : (s' f) = (s' f).
Proof. exact (eq_refl (s' f)). Qed.
Lemma lem3706871 {A B : Type'} (s' : type525 A B) (f : A -> B) : (term617 A B s' f) = (term618 A B s' f).
Proof. exact (MK_COMB (@lem3706869 A B f) (@lem3706870 A B s' f)). Qed.
Lemma lem3706872 {A B : Type'} (s' : type525 A B) (f : A -> B) : (term618 A B s' f) = (term619 A B s' f).
Proof. exact (eq_refl (term618 A B s' f)). Qed.
Lemma lem3706873 {A B : Type'} (s' : type525 A B) (f : A -> B) : (term617 A B s' f) = (term619 A B s' f).
Proof. exact (TRANS (@lem3706871 A B s' f) (@lem3706872 A B s' f)). Qed.
Lemma lem3706874 {A B : Type'} (s' : type525 A B) : (term620 A B s') = (term621 A B s').
Proof. exact (fun_ext (fun f : A -> B => @lem3706873 A B s' f)). Qed.
Lemma lem3706875 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3706876 {A B : Type'} (s' : type525 A B) : (term622 A B s') = (term623 A B s').
Proof. exact (MK_COMB (@lem3706875 A B) (@lem3706874 A B s')). Qed.
Lemma lem3706877 {A B : Type'} : (term624 A B) = (term625 A B).
Proof. exact (fun_ext (fun s' : type525 A B => @lem3706876 A B s')). Qed.
Lemma lem3706878 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3706879 {A B : Type'} : (term607 A B) = (term626 A B).
Proof. exact (MK_COMB (@lem3706878 A B) (@lem3706877 A B)). Qed.
Lemma lem3706880 {A B : Type'} : ((term606 A B) = (term607 A B)) = ((term603 A B) = (term626 A B)).
Proof. exact (MK_COMB (@lem3706868 A B) (@lem3706879 A B)). Qed.
Lemma lem3706881 {A B : Type'} : (term603 A B) = (term626 A B).
Proof. exact (EQ_MP (@lem3706880 A B) (@lem3706855 A B)). Qed.
Lemma lem3706882 {A B : Type'} : (term539 A B) = (term626 A B).
Proof. exact (TRANS (@lem3706851 A B) (@lem3706881 A B)). Qed.
Lemma lem3706883 {A B : Type'} : (term536 A B) = (term536 A B).
Proof. exact (eq_refl (term536 A B)). Qed.
Lemma lem3706884 {A B : Type'} : (term540 A B) = (term627 A B).
Proof. exact (MK_COMB (@lem3706883 A B) (@lem3706882 A B)). Qed.
Lemma lem3706886 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3706887 {A B : Type'} (P : Prop) (Q : type99 A B) : (term628 A B P Q) = (term629 A B P Q).
Proof. exact (@lem3706886 (type525 A B) P Q). Qed.
Lemma lem3706888 {A B : Type'} : (term630 A B) = (term631 A B).
Proof. exact (@lem3706887 A B (term534 A B) (term625 A B)). Qed.
Lemma lem3706889 {A B : Type'} (s' : type525 A B) : (term632 A B s') = (term623 A B s').
Proof. exact (eq_refl (term632 A B s')). Qed.
Lemma lem3706890 {A B : Type'} : (term633 A B) = (term625 A B).
Proof. exact (fun_ext (fun s' : type525 A B => @lem3706889 A B s')). Qed.
Lemma lem3706891 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3706892 {A B : Type'} : (term634 A B) = (term626 A B).
Proof. exact (MK_COMB (@lem3706891 A B) (@lem3706890 A B)). Qed.
Lemma lem3706893 {A B : Type'} : (term536 A B) = (term536 A B).
Proof. exact (eq_refl (term536 A B)). Qed.
Lemma lem3706894 {A B : Type'} : (term630 A B) = (term627 A B).
Proof. exact (MK_COMB (@lem3706893 A B) (@lem3706892 A B)). Qed.
Lemma lem3706895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706896 {A B : Type'} : (term635 A B) = (term636 A B).
Proof. exact (MK_COMB (@lem3706895) (@lem3706894 A B)). Qed.
Lemma lem3706897 {A B : Type'} (s' : type525 A B) : (term632 A B s') = (term623 A B s').
Proof. exact (eq_refl (term632 A B s')). Qed.
Lemma lem3706898 {A B : Type'} : (term536 A B) = (term536 A B).
Proof. exact (eq_refl (term536 A B)). Qed.
Lemma lem3706899 {A B : Type'} (s' : type525 A B) : (term637 A B s') = (term638 A B s').
Proof. exact (MK_COMB (@lem3706898 A B) (@lem3706897 A B s')). Qed.
Lemma lem3706900 {A B : Type'} : (term639 A B) = (term640 A B).
Proof. exact (fun_ext (fun s' : type525 A B => @lem3706899 A B s')). Qed.
Lemma lem3706901 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3706902 {A B : Type'} : (term631 A B) = (term641 A B).
Proof. exact (MK_COMB (@lem3706901 A B) (@lem3706900 A B)). Qed.
Lemma lem3706903 {A B : Type'} : ((term630 A B) = (term631 A B)) = ((term627 A B) = (term641 A B)).
Proof. exact (MK_COMB (@lem3706896 A B) (@lem3706902 A B)). Qed.
Lemma lem3706904 {A B : Type'} : (term627 A B) = (term641 A B).
Proof. exact (EQ_MP (@lem3706903 A B) (@lem3706888 A B)). Qed.
Lemma lem3706905 {A B : Type'} : (term540 A B) = (term641 A B).
Proof. exact (TRANS (@lem3706884 A B) (@lem3706904 A B)). Qed.
Lemma lem3706906 {A B : Type'} : (term474 A B) = (term641 A B).
Proof. exact (TRANS (@lem3706760 A B) (@lem3706905 A B)). Qed.
Lemma lem3706907 {A B : Type'} : (term11 A B) = (term641 A B).
Proof. exact (TRANS (@lem3706123 A B) (@lem3706906 A B)). Qed.
Lemma lem3706908 {A B : Type'} (h1 : term11 A B) : term641 A B.
Proof. exact (EQ_MP (@lem3706907 A B) (@lem3704371 A B h1)). Qed.
Lemma lem3706917 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term236 B t f s) = (term237 B t f s).
Proof. exact (@lem17045 (@FINITE B t) (term238 B t f s)). Qed.
Lemma lem3706931 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term239 B s t f s') = (term240 B s t f s').
Proof. exact (@lem17045 (@SUBSET B s' s) (t = (@IMAGE B B f s'))). Qed.
Lemma lem3706936 {B : Type'} (s' : B -> Prop) : (term82 B s') = (term82 B s').
Proof. exact (eq_refl (term82 B s')). Qed.
Lemma lem3706937 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term241 B s t f s') = (term242 B s t f s').
Proof. exact (MK_COMB (@lem3706936 B s') (@lem3706931 B s t f s')). Qed.
Lemma lem3706938 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term243 B s t f s') = (term241 B s t f s').
Proof. exact (@lem17045 (@FINITE B s') (term244 B s t f s')). Qed.
Lemma lem3706939 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term243 B s t f s') = (term242 B s t f s').
Proof. exact (TRANS (@lem3706938 B s t f s') (@lem3706937 B s t f s')). Qed.
Lemma lem3706942 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term43 B s t f s') = (term43 B s t f s').
Proof. exact (eq_refl (term43 B s t f s')). Qed.
Lemma lem3706943 {B : Type'} (P : type686 B) : (term87 B P) = (term88 B P).
Proof. exact (@lem18394 (B -> Prop) P). Qed.
Lemma lem3706944 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term245 B s t f) = (term246 B s t f).
Proof. exact (@lem3706943 B (term44 B s t f)). Qed.
Lemma lem3706945 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term247 B s t f s') = (term43 B s t f s').
Proof. exact (eq_refl (term247 B s t f s')). Qed.
Lemma lem3706946 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3706947 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term248 B s t f s') = (term243 B s t f s').
Proof. exact (MK_COMB (@lem3706946) (@lem3706945 B s t f s')). Qed.
Lemma lem3706948 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term248 B s t f s') = (term242 B s t f s').
Proof. exact (TRANS (@lem3706947 B s t f s') (@lem3706939 B s t f s')). Qed.
Lemma lem3706949 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term249 B s t f) = (term250 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3706948 B s t f s')). Qed.
Lemma lem3706950 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706951 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term246 B s t f) = (term251 B s t f).
Proof. exact (MK_COMB (@lem3706950 B) (@lem3706949 B s t f)). Qed.
Lemma lem3706952 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term245 B s t f) = (term251 B s t f).
Proof. exact (TRANS (@lem3706944 B s t f) (@lem3706951 B s t f)). Qed.
Lemma lem3706953 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term44 B s t f) = (term44 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3706942 B s t f s')). Qed.
Lemma lem3706954 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3706955 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term45 B s t f) = (term45 B s t f).
Proof. exact (MK_COMB (@lem3706954 B) (@lem3706953 B s t f)). Qed.
Lemma lem3706956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3706957 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term252 B t f s) = (term253 B t f s).
Proof. exact (MK_COMB (@lem3706956) (@lem3706917 B t f s)). Qed.
Lemma lem3706958 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term254 B s t f) = (term255 B s t f).
Proof. exact (MK_COMB (@lem3706957 B t f s) (@lem3706955 B s t f)). Qed.
Lemma lem3706960 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term256 B t f s) = (term256 B t f s).
Proof. exact (eq_refl (term256 B t f s)). Qed.
Lemma lem3706961 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term257 B s t f) = (term258 B s t f).
Proof. exact (MK_COMB (@lem3706960 B t f s) (@lem3706952 B s t f)). Qed.
Lemma lem3706962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706963 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term259 B s t f) = (term260 B s t f).
Proof. exact (MK_COMB (@lem3706962) (@lem3706961 B s t f)). Qed.
Lemma lem3706964 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term261 B s t f) = (term262 B s t f).
Proof. exact (MK_COMB (@lem3706963 B s t f) (@lem3706958 B s t f)). Qed.
Lemma lem3706965 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term47 B t f s) = (term45 B s t f)) = (term261 B s t f).
Proof. exact (@lem17784 (term47 B t f s) (term45 B s t f)). Qed.
Lemma lem3706966 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term47 B t f s) = (term45 B s t f)) = (term262 B s t f).
Proof. exact (TRANS (@lem3706965 B s t f) (@lem3706964 B s t f)). Qed.
Lemma lem3706967 {B : Type'} (s : B -> Prop) (f : B -> B) : (term48 B s f) = (term263 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706966 B s t f)). Qed.
Lemma lem3706968 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706969 {B : Type'} (s : B -> Prop) (f : B -> B) : (term49 B s f) = (term264 B s f).
Proof. exact (MK_COMB (@lem3706968 B) (@lem3706967 B s f)). Qed.
Lemma lem3706970 {B : Type'} (f : B -> B) : (term50 B f) = (term265 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3706969 B s f)). Qed.
Lemma lem3706971 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706972 {B : Type'} (f : B -> B) : (term51 B f) = (term266 B f).
Proof. exact (MK_COMB (@lem3706971 B) (@lem3706970 B f)). Qed.
Lemma lem3706973 {B : Type'} : (term52 B) = (term267 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3706972 B f)). Qed.
Lemma lem3706974 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3706975 {B : Type'} : (term12 B) = (term268 B).
Proof. exact (MK_COMB (@lem3706974 B) (@lem3706973 B)). Qed.
Lemma lem3706985 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3706986 {B : Type'} (P : type686 B) (Q : type686 B) : (term271 B P Q) = (term272 B P Q).
Proof. exact (@lem3706985 (B -> Prop) P Q). Qed.
Lemma lem3706987 {B : Type'} (s : B -> Prop) (f : B -> B) : (term273 B s f) = (term274 B s f).
Proof. exact (@lem3706986 B (term275 B s f) (term276 B s f)). Qed.
Lemma lem3706988 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term277 B s f t) = (term258 B s t f).
Proof. exact (eq_refl (term277 B s f t)). Qed.
Lemma lem3706989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3706990 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term278 B s f t) = (term260 B s t f).
Proof. exact (MK_COMB (@lem3706989) (@lem3706988 B s t f)). Qed.
Lemma lem3706991 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term279 B s f t) = (term255 B s t f).
Proof. exact (eq_refl (term279 B s f t)). Qed.
Lemma lem3706992 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term280 B s f t) = (term262 B s t f).
Proof. exact (MK_COMB (@lem3706990 B s t f) (@lem3706991 B s t f)). Qed.
Lemma lem3706993 {B : Type'} (s : B -> Prop) (f : B -> B) : (term281 B s f) = (term263 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706992 B s t f)). Qed.
Lemma lem3706994 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3706995 {B : Type'} (s : B -> Prop) (f : B -> B) : (term273 B s f) = (term264 B s f).
Proof. exact (MK_COMB (@lem3706994 B) (@lem3706993 B s f)). Qed.
Lemma lem3706996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3706997 {B : Type'} (s : B -> Prop) (f : B -> B) : (term282 B s f) = (term283 B s f).
Proof. exact (MK_COMB (@lem3706996) (@lem3706995 B s f)). Qed.
Lemma lem3706998 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term277 B s f t) = (term258 B s t f).
Proof. exact (eq_refl (term277 B s f t)). Qed.
Lemma lem3706999 {B : Type'} (s : B -> Prop) (f : B -> B) : (term284 B s f) = (term275 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3706998 B s t f)). Qed.
Lemma lem3707000 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707001 {B : Type'} (s : B -> Prop) (f : B -> B) : (term285 B s f) = (term286 B s f).
Proof. exact (MK_COMB (@lem3707000 B) (@lem3706999 B s f)). Qed.
Lemma lem3707002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3707003 {B : Type'} (s : B -> Prop) (f : B -> B) : (term287 B s f) = (term288 B s f).
Proof. exact (MK_COMB (@lem3707002) (@lem3707001 B s f)). Qed.
Lemma lem3707004 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term279 B s f t) = (term255 B s t f).
Proof. exact (eq_refl (term279 B s f t)). Qed.
Lemma lem3707005 {B : Type'} (s : B -> Prop) (f : B -> B) : (term289 B s f) = (term276 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3707004 B s t f)). Qed.
Lemma lem3707006 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707007 {B : Type'} (s : B -> Prop) (f : B -> B) : (term290 B s f) = (term291 B s f).
Proof. exact (MK_COMB (@lem3707006 B) (@lem3707005 B s f)). Qed.
Lemma lem3707008 {B : Type'} (s : B -> Prop) (f : B -> B) : (term274 B s f) = (term292 B s f).
Proof. exact (MK_COMB (@lem3707003 B s f) (@lem3707007 B s f)). Qed.
Lemma lem3707009 {B : Type'} (s : B -> Prop) (f : B -> B) : ((term273 B s f) = (term274 B s f)) = ((term264 B s f) = (term292 B s f)).
Proof. exact (MK_COMB (@lem3706997 B s f) (@lem3707008 B s f)). Qed.
Lemma lem3707010 {B : Type'} (s : B -> Prop) (f : B -> B) : (term264 B s f) = (term292 B s f).
Proof. exact (EQ_MP (@lem3707009 B s f) (@lem3706987 B s f)). Qed.
Lemma lem3707183 {B : Type'} (f : B -> B) : (term265 B f) = (term293 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707010 B s f)). Qed.
Lemma lem3707184 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707185 {B : Type'} (f : B -> B) : (term266 B f) = (term294 B f).
Proof. exact (MK_COMB (@lem3707184 B) (@lem3707183 B f)). Qed.
Lemma lem3707187 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3707188 {B : Type'} (P : type686 B) (Q : type686 B) : (term271 B P Q) = (term272 B P Q).
Proof. exact (@lem3707187 (B -> Prop) P Q). Qed.
Lemma lem3707189 {B : Type'} (f : B -> B) : (term295 B f) = (term296 B f).
Proof. exact (@lem3707188 B (term297 B f) (term298 B f)). Qed.
Lemma lem3707190 {B : Type'} (s : B -> Prop) (f : B -> B) : (term299 B f s) = (term286 B s f).
Proof. exact (eq_refl (term299 B f s)). Qed.
Lemma lem3707191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3707192 {B : Type'} (s : B -> Prop) (f : B -> B) : (term300 B f s) = (term288 B s f).
Proof. exact (MK_COMB (@lem3707191) (@lem3707190 B s f)). Qed.
Lemma lem3707193 {B : Type'} (s : B -> Prop) (f : B -> B) : (term301 B f s) = (term291 B s f).
Proof. exact (eq_refl (term301 B f s)). Qed.
Lemma lem3707194 {B : Type'} (s : B -> Prop) (f : B -> B) : (term302 B f s) = (term292 B s f).
Proof. exact (MK_COMB (@lem3707192 B s f) (@lem3707193 B s f)). Qed.
Lemma lem3707195 {B : Type'} (f : B -> B) : (term303 B f) = (term293 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707194 B s f)). Qed.
Lemma lem3707196 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707197 {B : Type'} (f : B -> B) : (term295 B f) = (term294 B f).
Proof. exact (MK_COMB (@lem3707196 B) (@lem3707195 B f)). Qed.
Lemma lem3707198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3707199 {B : Type'} (f : B -> B) : (term304 B f) = (term305 B f).
Proof. exact (MK_COMB (@lem3707198) (@lem3707197 B f)). Qed.
Lemma lem3707200 {B : Type'} (s : B -> Prop) (f : B -> B) : (term299 B f s) = (term286 B s f).
Proof. exact (eq_refl (term299 B f s)). Qed.
Lemma lem3707201 {B : Type'} (f : B -> B) : (term306 B f) = (term297 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707200 B s f)). Qed.
Lemma lem3707202 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707203 {B : Type'} (f : B -> B) : (term307 B f) = (term308 B f).
Proof. exact (MK_COMB (@lem3707202 B) (@lem3707201 B f)). Qed.
Lemma lem3707204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3707205 {B : Type'} (f : B -> B) : (term309 B f) = (term310 B f).
Proof. exact (MK_COMB (@lem3707204) (@lem3707203 B f)). Qed.
Lemma lem3707206 {B : Type'} (s : B -> Prop) (f : B -> B) : (term301 B f s) = (term291 B s f).
Proof. exact (eq_refl (term301 B f s)). Qed.
Lemma lem3707207 {B : Type'} (f : B -> B) : (term311 B f) = (term298 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707206 B s f)). Qed.
Lemma lem3707208 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707209 {B : Type'} (f : B -> B) : (term312 B f) = (term313 B f).
Proof. exact (MK_COMB (@lem3707208 B) (@lem3707207 B f)). Qed.
Lemma lem3707210 {B : Type'} (f : B -> B) : (term296 B f) = (term314 B f).
Proof. exact (MK_COMB (@lem3707205 B f) (@lem3707209 B f)). Qed.
Lemma lem3707211 {B : Type'} (f : B -> B) : ((term295 B f) = (term296 B f)) = ((term294 B f) = (term314 B f)).
Proof. exact (MK_COMB (@lem3707199 B f) (@lem3707210 B f)). Qed.
Lemma lem3707212 {B : Type'} (f : B -> B) : (term294 B f) = (term314 B f).
Proof. exact (EQ_MP (@lem3707211 B f) (@lem3707189 B f)). Qed.
Lemma lem3707393 {B : Type'} (f : B -> B) : (term266 B f) = (term314 B f).
Proof. exact (TRANS (@lem3707185 B f) (@lem3707212 B f)). Qed.
Lemma lem3707394 {B : Type'} : (term267 B) = (term315 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3707393 B f)). Qed.
Lemma lem3707395 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3707396 {B : Type'} : (term268 B) = (term316 B).
Proof. exact (MK_COMB (@lem3707395 B) (@lem3707394 B)). Qed.
Lemma lem3707398 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3707399 {B : Type'} (P : type488 B) (Q : type488 B) : (term317 B P Q) = (term318 B P Q).
Proof. exact (@lem3707398 (B -> B) P Q). Qed.
Lemma lem3707400 {B : Type'} : (term319 B) = (term320 B).
Proof. exact (@lem3707399 B (term321 B) (term322 B)). Qed.
Lemma lem3707401 {B : Type'} (f : B -> B) : (term323 B f) = (term308 B f).
Proof. exact (eq_refl (term323 B f)). Qed.
Lemma lem3707402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3707403 {B : Type'} (f : B -> B) : (term324 B f) = (term310 B f).
Proof. exact (MK_COMB (@lem3707402) (@lem3707401 B f)). Qed.
Lemma lem3707404 {B : Type'} (f : B -> B) : (term325 B f) = (term313 B f).
Proof. exact (eq_refl (term325 B f)). Qed.
Lemma lem3707405 {B : Type'} (f : B -> B) : (term326 B f) = (term314 B f).
Proof. exact (MK_COMB (@lem3707403 B f) (@lem3707404 B f)). Qed.
Lemma lem3707406 {B : Type'} : (term327 B) = (term315 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3707405 B f)). Qed.
Lemma lem3707407 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3707408 {B : Type'} : (term319 B) = (term316 B).
Proof. exact (MK_COMB (@lem3707407 B) (@lem3707406 B)). Qed.
Lemma lem3707409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3707410 {B : Type'} : (term328 B) = (term329 B).
Proof. exact (MK_COMB (@lem3707409) (@lem3707408 B)). Qed.
Lemma lem3707411 {B : Type'} (f : B -> B) : (term323 B f) = (term308 B f).
Proof. exact (eq_refl (term323 B f)). Qed.
Lemma lem3707412 {B : Type'} : (term330 B) = (term321 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3707411 B f)). Qed.
Lemma lem3707413 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3707414 {B : Type'} : (term331 B) = (term332 B).
Proof. exact (MK_COMB (@lem3707413 B) (@lem3707412 B)). Qed.
Lemma lem3707415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3707416 {B : Type'} : (term333 B) = (term334 B).
Proof. exact (MK_COMB (@lem3707415) (@lem3707414 B)). Qed.
Lemma lem3707417 {B : Type'} (f : B -> B) : (term325 B f) = (term313 B f).
Proof. exact (eq_refl (term325 B f)). Qed.
Lemma lem3707418 {B : Type'} : (term335 B) = (term322 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3707417 B f)). Qed.
Lemma lem3707419 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3707420 {B : Type'} : (term336 B) = (term337 B).
Proof. exact (MK_COMB (@lem3707419 B) (@lem3707418 B)). Qed.
Lemma lem3707421 {B : Type'} : (term320 B) = (term338 B).
Proof. exact (MK_COMB (@lem3707416 B) (@lem3707420 B)). Qed.
Lemma lem3707422 {B : Type'} : ((term319 B) = (term320 B)) = ((term316 B) = (term338 B)).
Proof. exact (MK_COMB (@lem3707410 B) (@lem3707421 B)). Qed.
Lemma lem3707423 {B : Type'} : (term316 B) = (term338 B).
Proof. exact (EQ_MP (@lem3707422 B) (@lem3707400 B)). Qed.
Lemma lem3707612 {B : Type'} : (term268 B) = (term338 B).
Proof. exact (TRANS (@lem3707396 B) (@lem3707423 B)). Qed.
Lemma lem3707614 {A : Type'} (P : Prop) (Q : A -> Prop) : (term216 A P Q) = (term217 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3707615 {B : Type'} (P : Prop) (Q : type686 B) : (term218 B P Q) = (term219 B P Q).
Proof. exact (@lem3707614 (B -> Prop) P Q). Qed.
Lemma lem3707616 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term339 B s t f) = (term340 B s t f).
Proof. exact (@lem3707615 B (term237 B t f s) (term44 B s t f)). Qed.
Lemma lem3707617 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term247 B s t f s') = (term43 B s t f s').
Proof. exact (eq_refl (term247 B s t f s')). Qed.
Lemma lem3707618 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term341 B s t f) = (term44 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3707617 B s t f s')). Qed.
Lemma lem3707619 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3707620 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term342 B s t f) = (term45 B s t f).
Proof. exact (MK_COMB (@lem3707619 B) (@lem3707618 B s t f)). Qed.
Lemma lem3707621 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term253 B t f s) = (term253 B t f s).
Proof. exact (eq_refl (term253 B t f s)). Qed.
Lemma lem3707622 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term339 B s t f) = (term255 B s t f).
Proof. exact (MK_COMB (@lem3707621 B t f s) (@lem3707620 B s t f)). Qed.
Lemma lem3707623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3707624 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term343 B s t f) = (term344 B s t f).
Proof. exact (MK_COMB (@lem3707623) (@lem3707622 B s t f)). Qed.
Lemma lem3707625 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term247 B s t f s') = (term43 B s t f s').
Proof. exact (eq_refl (term247 B s t f s')). Qed.
Lemma lem3707626 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term253 B t f s) = (term253 B t f s).
Proof. exact (eq_refl (term253 B t f s)). Qed.
Lemma lem3707627 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term345 B s t f s') = (term346 B s t f s').
Proof. exact (MK_COMB (@lem3707626 B t f s) (@lem3707625 B s t f s')). Qed.
Lemma lem3707628 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term347 B s t f) = (term348 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3707627 B s t f s')). Qed.
Lemma lem3707629 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3707630 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term340 B s t f) = (term349 B s t f).
Proof. exact (MK_COMB (@lem3707629 B) (@lem3707628 B s t f)). Qed.
Lemma lem3707631 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term339 B s t f) = (term340 B s t f)) = ((term255 B s t f) = (term349 B s t f)).
Proof. exact (MK_COMB (@lem3707624 B s t f) (@lem3707630 B s t f)). Qed.
Lemma lem3707632 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term255 B s t f) = (term349 B s t f).
Proof. exact (EQ_MP (@lem3707631 B s t f) (@lem3707616 B s t f)). Qed.
Lemma lem3707633 {B : Type'} (s : B -> Prop) (f : B -> B) : (term276 B s f) = (term350 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3707632 B s t f)). Qed.
Lemma lem3707634 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707635 {B : Type'} (s : B -> Prop) (f : B -> B) : (term291 B s f) = (term351 B s f).
Proof. exact (MK_COMB (@lem3707634 B) (@lem3707633 B s f)). Qed.
Lemma lem3707637 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3707638 {B : Type'} (P : type639 B) : (term354 B P) = (term355 B P).
Proof. exact (@lem3707637 (B -> Prop) (B -> Prop) P). Qed.
Lemma lem3707639 {B : Type'} (s : B -> Prop) (f : B -> B) : (term356 B s f) = (term357 B s f).
Proof. exact (@lem3707638 B (term358 B s f)). Qed.
Lemma lem3707640 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term359 B s f t) = (term348 B s t f).
Proof. exact (eq_refl (term359 B s f t)). Qed.
Lemma lem3707641 {B : Type'} (s' : B -> Prop) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3707642 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term360 B s f t s') = (term361 B s t f s').
Proof. exact (MK_COMB (@lem3707640 B s t f) (@lem3707641 B s')). Qed.
Lemma lem3707643 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term361 B s t f s') = (term346 B s t f s').
Proof. exact (eq_refl (term361 B s t f s')). Qed.
Lemma lem3707644 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term360 B s f t s') = (term346 B s t f s').
Proof. exact (TRANS (@lem3707642 B s t f s') (@lem3707643 B s t f s')). Qed.
Lemma lem3707645 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term362 B s f t) = (term348 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3707644 B s t f s')). Qed.
Lemma lem3707646 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3707647 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term363 B s f t) = (term349 B s t f).
Proof. exact (MK_COMB (@lem3707646 B) (@lem3707645 B s t f)). Qed.
Lemma lem3707648 {B : Type'} (s : B -> Prop) (f : B -> B) : (term364 B s f) = (term350 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3707647 B s t f)). Qed.
Lemma lem3707649 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707650 {B : Type'} (s : B -> Prop) (f : B -> B) : (term356 B s f) = (term351 B s f).
Proof. exact (MK_COMB (@lem3707649 B) (@lem3707648 B s f)). Qed.
Lemma lem3707651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3707652 {B : Type'} (s : B -> Prop) (f : B -> B) : (term365 B s f) = (term366 B s f).
Proof. exact (MK_COMB (@lem3707651) (@lem3707650 B s f)). Qed.
Lemma lem3707653 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term359 B s f t) = (term348 B s t f).
Proof. exact (eq_refl (term359 B s f t)). Qed.
Lemma lem3707654 {B : Type'} (s' : type672 B) (t : B -> Prop) : (s' t) = (s' t).
Proof. exact (eq_refl (s' t)). Qed.
Lemma lem3707655 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) (t : B -> Prop) : (term367 B s f s' t) = (term368 B s f s' t).
Proof. exact (MK_COMB (@lem3707653 B s t f) (@lem3707654 B s' t)). Qed.
Lemma lem3707656 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) (t : B -> Prop) : (term368 B s f s' t) = (term369 B s f s' t).
Proof. exact (eq_refl (term368 B s f s' t)). Qed.
Lemma lem3707657 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) (t : B -> Prop) : (term367 B s f s' t) = (term369 B s f s' t).
Proof. exact (TRANS (@lem3707655 B s f s' t) (@lem3707656 B s f s' t)). Qed.
Lemma lem3707658 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term370 B s f s') = (term371 B s f s').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3707657 B s f s' t)). Qed.
Lemma lem3707659 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707660 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term372 B s f s') = (term373 B s f s').
Proof. exact (MK_COMB (@lem3707659 B) (@lem3707658 B s f s')). Qed.
Lemma lem3707661 {B : Type'} (s : B -> Prop) (f : B -> B) : (term374 B s f) = (term375 B s f).
Proof. exact (fun_ext (fun s' : type672 B => @lem3707660 B s f s')). Qed.
Lemma lem3707662 {B : Type'} : (@ex ((B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B -> Prop))). Qed.
Lemma lem3707663 {B : Type'} (s : B -> Prop) (f : B -> B) : (term357 B s f) = (term376 B s f).
Proof. exact (MK_COMB (@lem3707662 B) (@lem3707661 B s f)). Qed.
Lemma lem3707664 {B : Type'} (s : B -> Prop) (f : B -> B) : ((term356 B s f) = (term357 B s f)) = ((term351 B s f) = (term376 B s f)).
Proof. exact (MK_COMB (@lem3707652 B s f) (@lem3707663 B s f)). Qed.
Lemma lem3707665 {B : Type'} (s : B -> Prop) (f : B -> B) : (term351 B s f) = (term376 B s f).
Proof. exact (EQ_MP (@lem3707664 B s f) (@lem3707639 B s f)). Qed.
Lemma lem3707666 {B : Type'} (s : B -> Prop) (f : B -> B) : (term291 B s f) = (term376 B s f).
Proof. exact (TRANS (@lem3707635 B s f) (@lem3707665 B s f)). Qed.
Lemma lem3707667 {B : Type'} (f : B -> B) : (term298 B f) = (term377 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707666 B s f)). Qed.
Lemma lem3707668 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707669 {B : Type'} (f : B -> B) : (term313 B f) = (term378 B f).
Proof. exact (MK_COMB (@lem3707668 B) (@lem3707667 B f)). Qed.
Lemma lem3707671 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3707672 {B : Type'} (P : type596 B) : (term379 B P) = (term380 B P).
Proof. exact (@lem3707671 (B -> Prop) (type672 B) P). Qed.
Lemma lem3707673 {B : Type'} (f : B -> B) : (term381 B f) = (term382 B f).
Proof. exact (@lem3707672 B (term383 B f)). Qed.
Lemma lem3707674 {B : Type'} (s : B -> Prop) (f : B -> B) : (term384 B f s) = (term375 B s f).
Proof. exact (eq_refl (term384 B f s)). Qed.
Lemma lem3707675 {B : Type'} (s' : type672 B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3707676 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term385 B f s s') = (term386 B s f s').
Proof. exact (MK_COMB (@lem3707674 B s f) (@lem3707675 B s')). Qed.
Lemma lem3707677 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term386 B s f s') = (term373 B s f s').
Proof. exact (eq_refl (term386 B s f s')). Qed.
Lemma lem3707678 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term385 B f s s') = (term373 B s f s').
Proof. exact (TRANS (@lem3707676 B s f s') (@lem3707677 B s f s')). Qed.
Lemma lem3707679 {B : Type'} (s : B -> Prop) (f : B -> B) : (term387 B f s) = (term375 B s f).
Proof. exact (fun_ext (fun s' : type672 B => @lem3707678 B s f s')). Qed.
Lemma lem3707680 {B : Type'} : (@ex ((B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B -> Prop))). Qed.
Lemma lem3707681 {B : Type'} (s : B -> Prop) (f : B -> B) : (term388 B f s) = (term376 B s f).
Proof. exact (MK_COMB (@lem3707680 B) (@lem3707679 B s f)). Qed.
Lemma lem3707682 {B : Type'} (f : B -> B) : (term389 B f) = (term377 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707681 B s f)). Qed.
Lemma lem3707683 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707684 {B : Type'} (f : B -> B) : (term381 B f) = (term378 B f).
Proof. exact (MK_COMB (@lem3707683 B) (@lem3707682 B f)). Qed.
Lemma lem3707685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3707686 {B : Type'} (f : B -> B) : (term390 B f) = (term391 B f).
Proof. exact (MK_COMB (@lem3707685) (@lem3707684 B f)). Qed.
Lemma lem3707687 {B : Type'} (s : B -> Prop) (f : B -> B) : (term384 B f s) = (term375 B s f).
Proof. exact (eq_refl (term384 B f s)). Qed.
Lemma lem3707688 {B : Type'} (s' : type636 B) (s : B -> Prop) : (s' s) = (s' s).
Proof. exact (eq_refl (s' s)). Qed.
Lemma lem3707689 {B : Type'} (f : B -> B) (s' : type636 B) (s : B -> Prop) : (term392 B f s' s) = (term393 B f s' s).
Proof. exact (MK_COMB (@lem3707687 B s f) (@lem3707688 B s' s)). Qed.
Lemma lem3707690 {B : Type'} (f : B -> B) (s' : type636 B) (s : B -> Prop) : (term393 B f s' s) = (term394 B f s' s).
Proof. exact (eq_refl (term393 B f s' s)). Qed.
Lemma lem3707691 {B : Type'} (f : B -> B) (s' : type636 B) (s : B -> Prop) : (term392 B f s' s) = (term394 B f s' s).
Proof. exact (TRANS (@lem3707689 B f s' s) (@lem3707690 B f s' s)). Qed.
Lemma lem3707692 {B : Type'} (f : B -> B) (s' : type636 B) : (term395 B f s') = (term396 B f s').
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707691 B f s' s)). Qed.
Lemma lem3707693 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707694 {B : Type'} (f : B -> B) (s' : type636 B) : (term397 B f s') = (term398 B f s').
Proof. exact (MK_COMB (@lem3707693 B) (@lem3707692 B f s')). Qed.
Lemma lem3707695 {B : Type'} (f : B -> B) : (term399 B f) = (term400 B f).
Proof. exact (fun_ext (fun s' : type636 B => @lem3707694 B f s')). Qed.
Lemma lem3707696 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3707697 {B : Type'} (f : B -> B) : (term382 B f) = (term401 B f).
Proof. exact (MK_COMB (@lem3707696 B) (@lem3707695 B f)). Qed.
Lemma lem3707698 {B : Type'} (f : B -> B) : ((term381 B f) = (term382 B f)) = ((term378 B f) = (term401 B f)).
Proof. exact (MK_COMB (@lem3707686 B f) (@lem3707697 B f)). Qed.
Lemma lem3707699 {B : Type'} (f : B -> B) : (term378 B f) = (term401 B f).
Proof. exact (EQ_MP (@lem3707698 B f) (@lem3707673 B f)). Qed.
Lemma lem3707700 {B : Type'} (f : B -> B) : (term313 B f) = (term401 B f).
Proof. exact (TRANS (@lem3707669 B f) (@lem3707699 B f)). Qed.
Lemma lem3707701 {B : Type'} : (term322 B) = (term402 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3707700 B f)). Qed.
Lemma lem3707702 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3707703 {B : Type'} : (term337 B) = (term403 B).
Proof. exact (MK_COMB (@lem3707702 B) (@lem3707701 B)). Qed.
Lemma lem3707705 {A B : Type'} (P : type1413 A B) : (term352 A B P) = (term353 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3707706 {B : Type'} (P : type480 B) : (term404 B P) = (term405 B P).
Proof. exact (@lem3707705 (B -> B) (type636 B) P). Qed.
Lemma lem3707707 {B : Type'} : (term406 B) = (term407 B).
Proof. exact (@lem3707706 B (term408 B)). Qed.
Lemma lem3707708 {B : Type'} (f : B -> B) : (term409 B f) = (term400 B f).
Proof. exact (eq_refl (term409 B f)). Qed.
Lemma lem3707709 {B : Type'} (s' : type636 B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3707710 {B : Type'} (f : B -> B) (s' : type636 B) : (term410 B f s') = (term411 B f s').
Proof. exact (MK_COMB (@lem3707708 B f) (@lem3707709 B s')). Qed.
Lemma lem3707711 {B : Type'} (f : B -> B) (s' : type636 B) : (term411 B f s') = (term398 B f s').
Proof. exact (eq_refl (term411 B f s')). Qed.
Lemma lem3707712 {B : Type'} (f : B -> B) (s' : type636 B) : (term410 B f s') = (term398 B f s').
Proof. exact (TRANS (@lem3707710 B f s') (@lem3707711 B f s')). Qed.
Lemma lem3707713 {B : Type'} (f : B -> B) : (term412 B f) = (term400 B f).
Proof. exact (fun_ext (fun s' : type636 B => @lem3707712 B f s')). Qed.
Lemma lem3707714 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3707715 {B : Type'} (f : B -> B) : (term413 B f) = (term401 B f).
Proof. exact (MK_COMB (@lem3707714 B) (@lem3707713 B f)). Qed.
Lemma lem3707716 {B : Type'} : (term414 B) = (term402 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3707715 B f)). Qed.
Lemma lem3707717 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3707718 {B : Type'} : (term406 B) = (term403 B).
Proof. exact (MK_COMB (@lem3707717 B) (@lem3707716 B)). Qed.
Lemma lem3707719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3707720 {B : Type'} : (term415 B) = (term416 B).
Proof. exact (MK_COMB (@lem3707719) (@lem3707718 B)). Qed.
Lemma lem3707721 {B : Type'} (f : B -> B) : (term409 B f) = (term400 B f).
Proof. exact (eq_refl (term409 B f)). Qed.
Lemma lem3707722 {B : Type'} (s' : type483 B) (f : B -> B) : (s' f) = (s' f).
Proof. exact (eq_refl (s' f)). Qed.
Lemma lem3707723 {B : Type'} (s' : type483 B) (f : B -> B) : (term417 B s' f) = (term418 B s' f).
Proof. exact (MK_COMB (@lem3707721 B f) (@lem3707722 B s' f)). Qed.
Lemma lem3707724 {B : Type'} (s' : type483 B) (f : B -> B) : (term418 B s' f) = (term419 B s' f).
Proof. exact (eq_refl (term418 B s' f)). Qed.
Lemma lem3707725 {B : Type'} (s' : type483 B) (f : B -> B) : (term417 B s' f) = (term419 B s' f).
Proof. exact (TRANS (@lem3707723 B s' f) (@lem3707724 B s' f)). Qed.
Lemma lem3707726 {B : Type'} (s' : type483 B) : (term420 B s') = (term421 B s').
Proof. exact (fun_ext (fun f : B -> B => @lem3707725 B s' f)). Qed.
Lemma lem3707727 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3707728 {B : Type'} (s' : type483 B) : (term422 B s') = (term423 B s').
Proof. exact (MK_COMB (@lem3707727 B) (@lem3707726 B s')). Qed.
Lemma lem3707729 {B : Type'} : (term424 B) = (term425 B).
Proof. exact (fun_ext (fun s' : type483 B => @lem3707728 B s')). Qed.
Lemma lem3707730 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3707731 {B : Type'} : (term407 B) = (term426 B).
Proof. exact (MK_COMB (@lem3707730 B) (@lem3707729 B)). Qed.
Lemma lem3707732 {B : Type'} : ((term406 B) = (term407 B)) = ((term403 B) = (term426 B)).
Proof. exact (MK_COMB (@lem3707720 B) (@lem3707731 B)). Qed.
Lemma lem3707733 {B : Type'} : (term403 B) = (term426 B).
Proof. exact (EQ_MP (@lem3707732 B) (@lem3707707 B)). Qed.
Lemma lem3707734 {B : Type'} : (term337 B) = (term426 B).
Proof. exact (TRANS (@lem3707703 B) (@lem3707733 B)). Qed.
Lemma lem3707735 {B : Type'} : (term334 B) = (term334 B).
Proof. exact (eq_refl (term334 B)). Qed.
Lemma lem3707736 {B : Type'} : (term338 B) = (term427 B).
Proof. exact (MK_COMB (@lem3707735 B) (@lem3707734 B)). Qed.
Lemma lem3707738 {A : Type'} (P : Prop) (Q : A -> Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3707739 {B : Type'} (P : Prop) (Q : type92 B) : (term428 B P Q) = (term429 B P Q).
Proof. exact (@lem3707738 (type483 B) P Q). Qed.
Lemma lem3707740 {B : Type'} : (term430 B) = (term431 B).
Proof. exact (@lem3707739 B (term332 B) (term425 B)). Qed.
Lemma lem3707741 {B : Type'} (s' : type483 B) : (term432 B s') = (term423 B s').
Proof. exact (eq_refl (term432 B s')). Qed.
Lemma lem3707742 {B : Type'} : (term433 B) = (term425 B).
Proof. exact (fun_ext (fun s' : type483 B => @lem3707741 B s')). Qed.
Lemma lem3707743 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3707744 {B : Type'} : (term434 B) = (term426 B).
Proof. exact (MK_COMB (@lem3707743 B) (@lem3707742 B)). Qed.
Lemma lem3707745 {B : Type'} : (term334 B) = (term334 B).
Proof. exact (eq_refl (term334 B)). Qed.
Lemma lem3707746 {B : Type'} : (term430 B) = (term427 B).
Proof. exact (MK_COMB (@lem3707745 B) (@lem3707744 B)). Qed.
Lemma lem3707747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3707748 {B : Type'} : (term435 B) = (term436 B).
Proof. exact (MK_COMB (@lem3707747) (@lem3707746 B)). Qed.
Lemma lem3707749 {B : Type'} (s' : type483 B) : (term432 B s') = (term423 B s').
Proof. exact (eq_refl (term432 B s')). Qed.
Lemma lem3707750 {B : Type'} : (term334 B) = (term334 B).
Proof. exact (eq_refl (term334 B)). Qed.
Lemma lem3707751 {B : Type'} (s' : type483 B) : (term437 B s') = (term438 B s').
Proof. exact (MK_COMB (@lem3707750 B) (@lem3707749 B s')). Qed.
Lemma lem3707752 {B : Type'} : (term439 B) = (term440 B).
Proof. exact (fun_ext (fun s' : type483 B => @lem3707751 B s')). Qed.
Lemma lem3707753 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3707754 {B : Type'} : (term431 B) = (term441 B).
Proof. exact (MK_COMB (@lem3707753 B) (@lem3707752 B)). Qed.
Lemma lem3707755 {B : Type'} : ((term430 B) = (term431 B)) = ((term427 B) = (term441 B)).
Proof. exact (MK_COMB (@lem3707748 B) (@lem3707754 B)). Qed.
Lemma lem3707756 {B : Type'} : (term427 B) = (term441 B).
Proof. exact (EQ_MP (@lem3707755 B) (@lem3707740 B)). Qed.
Lemma lem3707757 {B : Type'} : (term338 B) = (term441 B).
Proof. exact (TRANS (@lem3707736 B) (@lem3707756 B)). Qed.
Lemma lem3707758 {B : Type'} : (term268 B) = (term441 B).
Proof. exact (TRANS (@lem3707612 B) (@lem3707757 B)). Qed.
Lemma lem3707759 {B : Type'} : (term12 B) = (term441 B).
Proof. exact (TRANS (@lem3706975 B) (@lem3707758 B)). Qed.
Lemma lem3707760 {B : Type'} (h1 : term12 B) : term441 B.
Proof. exact (EQ_MP (@lem3707759 B) (@lem3704372 B h1)). Qed.
Lemma lem3707762 {A B : Type'} (s'' : type525 A B) (h1 : term638 A B s'') : term638 A B s''.
Proof. exact (h1). Qed.
Lemma lem3707764 {A B : Type'} (f : A -> B) (h1 : term233 A B f) : term233 A B f.
Proof. exact (h1). Qed.
Lemma lem3707765 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term231 A B s f) : term231 A B s f.
Proof. exact (h1). Qed.
Lemma lem3707766 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term228 A B s f t) : term228 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3707780 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3707781 {B : Type'} : (term71 B) = (term71 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3707780 B s)). Qed.
Lemma lem3707782 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3707783 {B : Type'} : (term15 B) = (term15 B).
Proof. exact (MK_COMB (@lem3707782 B) (@lem3707781 B)). Qed.
Lemma lem3707784 {B : Type'} (h1 : term15 B) : term15 B.
Proof. exact (EQ_MP (@lem3707783 B) (@lem3704994 B h1)). Qed.
Lemma lem3708048 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term642 A B s'' f s t) = (term642 A B s'' f s t).
Proof. exact (eq_refl (term642 A B s'' f s t)). Qed.
Lemma lem3708049 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term643 A B s'' f s) = (term643 A B s'' f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3708048 A B s'' f s t)). Qed.
Lemma lem3708050 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3708051 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term644 A B s'' f s) = (term644 A B s'' f s).
Proof. exact (MK_COMB (@lem3708050 B) (@lem3708049 A B s'' f s)). Qed.
Lemma lem3708052 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term645 A B s'' f) = (term645 A B s'' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3708051 A B s'' f s)). Qed.
Lemma lem3708053 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708054 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term619 A B s'' f) = (term619 A B s'' f).
Proof. exact (MK_COMB (@lem3708053 A) (@lem3708052 A B s'' f)). Qed.
Lemma lem3708055 {A B : Type'} (s'' : type525 A B) : (term621 A B s'') = (term621 A B s'').
Proof. exact (fun_ext (fun f : A -> B => @lem3708054 A B s'' f)). Qed.
Lemma lem3708056 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3708057 {A B : Type'} (s'' : type525 A B) : (term623 A B s'') = (term623 A B s'').
Proof. exact (MK_COMB (@lem3708056 A B) (@lem3708055 A B s'')). Qed.
Lemma lem3708086 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term448 A B s t f s') = (term448 A B s t f s').
Proof. exact (eq_refl (term448 A B s t f s')). Qed.
Lemma lem3708087 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term456 A B s t f) = (term456 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3708086 A B s t f s')). Qed.
Lemma lem3708088 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708089 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term457 A B s t f) = (term457 A B s t f).
Proof. exact (MK_COMB (@lem3708088 A) (@lem3708087 A B s t f)). Qed.
Lemma lem3708106 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term462 A B t f s) = (term462 A B t f s).
Proof. exact (eq_refl (term462 A B t f s)). Qed.
Lemma lem3708107 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term464 A B s t f) = (term464 A B s t f).
Proof. exact (MK_COMB (@lem3708106 A B t f s) (@lem3708089 A B s t f)). Qed.
Lemma lem3708108 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term477 A B s f) = (term477 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3708107 A B s t f)). Qed.
Lemma lem3708109 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3708110 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term488 A B s f) = (term488 A B s f).
Proof. exact (MK_COMB (@lem3708109 B) (@lem3708108 A B s f)). Qed.
Lemma lem3708111 {A B : Type'} (f : A -> B) : (term499 A B f) = (term499 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3708110 A B s f)). Qed.
Lemma lem3708112 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708113 {A B : Type'} (f : A -> B) : (term510 A B f) = (term510 A B f).
Proof. exact (MK_COMB (@lem3708112 A) (@lem3708111 A B f)). Qed.
Lemma lem3708114 {A B : Type'} : (term523 A B) = (term523 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3708113 A B f)). Qed.
Lemma lem3708115 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3708116 {A B : Type'} : (term534 A B) = (term534 A B).
Proof. exact (MK_COMB (@lem3708115 A B) (@lem3708114 A B)). Qed.
Lemma lem3708117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3708118 {A B : Type'} : (term536 A B) = (term536 A B).
Proof. exact (MK_COMB (@lem3708117) (@lem3708116 A B)). Qed.
Lemma lem3708119 {A B : Type'} (s'' : type525 A B) : (term638 A B s'') = (term638 A B s'').
Proof. exact (MK_COMB (@lem3708118 A B) (@lem3708057 A B s'')). Qed.
Lemma lem3708120 {A B : Type'} (s'' : type525 A B) (h1 : term638 A B s'') : term638 A B s''.
Proof. exact (EQ_MP (@lem3708119 A B s'') (@lem3707762 A B s'' h1)). Qed.
Lemma lem3708294 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term183 A B s f t) = (term183 A B s f t).
Proof. exact (eq_refl (term183 A B s f t)). Qed.
Lemma lem3708327 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term84 A B s f t) = (term84 A B s f t).
Proof. exact (eq_refl (term84 A B s f t)). Qed.
Lemma lem3708328 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term94 A B s f) = (term94 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3708327 A B s f t)). Qed.
Lemma lem3708329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708330 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term95 A B s f) = (term95 A B s f).
Proof. exact (MK_COMB (@lem3708329 A) (@lem3708328 A B s f)). Qed.
Lemma lem3708339 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term98 A B f s) = (term98 A B f s).
Proof. exact (eq_refl (term98 A B f s)). Qed.
Lemma lem3708340 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term100 A B s f) = (term100 A B s f).
Proof. exact (MK_COMB (@lem3708339 A B f s) (@lem3708330 A B s f)). Qed.
Lemma lem3708341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3708342 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term102 A B s f) = (term102 A B s f).
Proof. exact (MK_COMB (@lem3708341) (@lem3708340 A B s f)). Qed.
Lemma lem3708343 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term228 A B s f t) = (term228 A B s f t).
Proof. exact (MK_COMB (@lem3708342 A B s f) (@lem3708294 A B s f t)). Qed.
Lemma lem3708344 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term228 A B s f t) : term228 A B s f t.
Proof. exact (EQ_MP (@lem3708343 A B s f t) (@lem3707766 A B s f t h1)). Qed.
Lemma lem3708347 {A B : Type'} (s'' : type525 A B) (h1 : term638 A B s'') : term623 A B s''.
Proof. exact (proj2 (@lem3708120 A B s'' h1)). Qed.
Lemma lem3708348 {A B : Type'} (s'' : type525 A B) (h1 : term638 A B s'') : term534 A B.
Proof. exact (proj1 (@lem3708120 A B s'' h1)). Qed.
Lemma lem3708351 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term100 A B s f.
Proof. exact (h1). Qed.
Lemma lem3708352 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term183 A B s f t.
Proof. exact (h1). Qed.
Lemma lem3708353 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term95 A B s f.
Proof. exact (proj2 (@lem3708351 A B s f h1)). Qed.
Lemma lem3708355 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term72 A B s f t.
Proof. exact (proj2 (@lem3708352 A B s f t h1)). Qed.
Lemma lem3708357 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term86 A B s f t.
Proof. exact (proj2 (@lem3708355 A B s f t h1)). Qed.
Lemma lem3708369 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3708370 {B : Type'} : (term71 B) = (term71 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3708369 B s)). Qed.
Lemma lem3708371 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3708373 {B : Type'} : (term15 B) = (term15 B).
Proof. exact (MK_COMB (@lem3708371 B) (@lem3708370 B)). Qed.
Lemma lem3708374 {B : Type'} (h1 : term15 B) : term15 B.
Proof. exact (EQ_MP (@lem3708373 B) (@lem3707784 B h1)). Qed.
Lemma lem3708632 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term642 A B s'' f s t) = (term646 A B s'' f s t).
Proof. exact (@lem19490 (term647 A B s'' f s t) (term443 A B t f s) (term648 A B s'' f s t)). Qed.
Lemma lem3708639 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term649 A B s'' f s t) = (term650 A B s'' f s t).
Proof. exact (@lem19490 (term651 A B s'' f t s) (term443 A B t f s) (t = (term652 A B s'' f s t))). Qed.
Lemma lem3708642 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term653 A B s'' f s t) = (term653 A B s'' f s t).
Proof. exact (eq_refl (term653 A B s'' f s t)). Qed.
Lemma lem3708643 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term646 A B s'' f s t) = (term654 A B s'' f s t).
Proof. exact (MK_COMB (@lem3708642 A B s'' f s t) (@lem3708639 A B s'' f s t)). Qed.
Lemma lem3708645 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term642 A B s'' f s t) = (term654 A B s'' f s t).
Proof. exact (TRANS (@lem3708632 A B s'' f s t) (@lem3708643 A B s'' f s t)). Qed.
Lemma lem3708646 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term643 A B s'' f s) = (term655 A B s'' f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3708645 A B s'' f s t)). Qed.
Lemma lem3708647 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3708648 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term644 A B s'' f s) = (term656 A B s'' f s).
Proof. exact (MK_COMB (@lem3708647 B) (@lem3708646 A B s'' f s)). Qed.
Lemma lem3708649 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term645 A B s'' f) = (term657 A B s'' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3708648 A B s'' f s)). Qed.
Lemma lem3708650 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708651 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term619 A B s'' f) = (term658 A B s'' f).
Proof. exact (MK_COMB (@lem3708650 A) (@lem3708649 A B s'' f)). Qed.
Lemma lem3708652 {A B : Type'} (s'' : type525 A B) : (term621 A B s'') = (term659 A B s'').
Proof. exact (fun_ext (fun f : A -> B => @lem3708651 A B s'' f)). Qed.
Lemma lem3708653 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3708655 {A B : Type'} (s'' : type525 A B) : (term623 A B s'') = (term660 A B s'').
Proof. exact (MK_COMB (@lem3708653 A B) (@lem3708652 A B s'')). Qed.
Lemma lem3708656 {A B : Type'} (s'' : type525 A B) (h1 : term638 A B s'') : term660 A B s''.
Proof. exact (EQ_MP (@lem3708655 A B s'') (@lem3708347 A B s'' h1)). Qed.
Lemma lem3708791 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term84 A B s f t) = (term84 A B s f t).
Proof. exact (eq_refl (term84 A B s f t)). Qed.
Lemma lem3708792 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term94 A B s f) = (term94 A B s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3708791 A B s f t)). Qed.
Lemma lem3708793 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708795 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term95 A B s f) = (term95 A B s f).
Proof. exact (MK_COMB (@lem3708793 A) (@lem3708792 A B s f)). Qed.
Lemma lem3708796 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term95 A B s f.
Proof. exact (EQ_MP (@lem3708795 A B s f) (@lem3708353 A B s f h1)). Qed.
Lemma lem3708977 {A : Type'} (P : Prop) (Q : A -> Prop) : (term661 A P Q) = (term662 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3708978 {A : Type'} (P : Prop) (Q : type686 A) : (term663 A P Q) = (term664 A P Q).
Proof. exact (@lem3708977 (A -> Prop) P Q). Qed.
Lemma lem3708979 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term665 A B s t f) = (term666 A B s t f).
Proof. exact (@lem3708978 A (term57 A B t f s) (term456 A B s t f)). Qed.
Lemma lem3708980 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term667 A B s t f s') = (term448 A B s t f s').
Proof. exact (eq_refl (term667 A B s t f s')). Qed.
Lemma lem3708981 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term668 A B s t f) = (term456 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3708980 A B s t f s')). Qed.
Lemma lem3708982 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708983 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term669 A B s t f) = (term457 A B s t f).
Proof. exact (MK_COMB (@lem3708982 A) (@lem3708981 A B s t f)). Qed.
Lemma lem3708984 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term462 A B t f s) = (term462 A B t f s).
Proof. exact (eq_refl (term462 A B t f s)). Qed.
Lemma lem3708985 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term665 A B s t f) = (term464 A B s t f).
Proof. exact (MK_COMB (@lem3708984 A B t f s) (@lem3708983 A B s t f)). Qed.
Lemma lem3708986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3708987 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term670 A B s t f) = (term671 A B s t f).
Proof. exact (MK_COMB (@lem3708986) (@lem3708985 A B s t f)). Qed.
Lemma lem3708988 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term667 A B s t f s') = (term448 A B s t f s').
Proof. exact (eq_refl (term667 A B s t f s')). Qed.
Lemma lem3708989 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term462 A B t f s) = (term462 A B t f s).
Proof. exact (eq_refl (term462 A B t f s)). Qed.
Lemma lem3708990 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term672 A B s t f s') = (term673 A B s t f s').
Proof. exact (MK_COMB (@lem3708989 A B t f s) (@lem3708988 A B s t f s')). Qed.
Lemma lem3708991 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term674 A B s t f) = (term675 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3708990 A B s t f s')). Qed.
Lemma lem3708992 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3708993 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term666 A B s t f) = (term676 A B s t f).
Proof. exact (MK_COMB (@lem3708992 A) (@lem3708991 A B s t f)). Qed.
Lemma lem3708994 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term665 A B s t f) = (term666 A B s t f)) = ((term464 A B s t f) = (term676 A B s t f)).
Proof. exact (MK_COMB (@lem3708987 A B s t f) (@lem3708993 A B s t f)). Qed.
Lemma lem3708995 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term464 A B s t f) = (term676 A B s t f).
Proof. exact (EQ_MP (@lem3708994 A B s t f) (@lem3708979 A B s t f)). Qed.
Lemma lem3708996 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term477 A B s f) = (term677 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3708995 A B s t f)). Qed.
Lemma lem3708997 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3708998 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term488 A B s f) = (term678 A B s f).
Proof. exact (MK_COMB (@lem3708997 B) (@lem3708996 A B s f)). Qed.
Lemma lem3708999 {A B : Type'} (f : A -> B) : (term499 A B f) = (term679 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3708998 A B s f)). Qed.
Lemma lem3709000 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3709001 {A B : Type'} (f : A -> B) : (term510 A B f) = (term680 A B f).
Proof. exact (MK_COMB (@lem3709000 A) (@lem3708999 A B f)). Qed.
Lemma lem3709002 {A B : Type'} : (term523 A B) = (term681 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3709001 A B f)). Qed.
Lemma lem3709003 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3709004 {A B : Type'} : (term534 A B) = (term682 A B).
Proof. exact (MK_COMB (@lem3709003 A B) (@lem3709002 A B)). Qed.
Lemma lem3709033 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term673 A B s t f s') = (term683 A B s t f s').
Proof. exact (@lem19699 (@FINITE B t) (term444 A B t f s) (term448 A B s t f s')). Qed.
Lemma lem3709034 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term675 A B s t f) = (term684 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3709033 A B s t f s')). Qed.
Lemma lem3709035 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3709036 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term676 A B s t f) = (term685 A B s t f).
Proof. exact (MK_COMB (@lem3709035 A) (@lem3709034 A B s t f)). Qed.
Lemma lem3709037 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term677 A B s f) = (term686 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3709036 A B s t f)). Qed.
Lemma lem3709038 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3709039 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term678 A B s f) = (term687 A B s f).
Proof. exact (MK_COMB (@lem3709038 B) (@lem3709037 A B s f)). Qed.
Lemma lem3709040 {A B : Type'} (f : A -> B) : (term679 A B f) = (term688 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3709039 A B s f)). Qed.
Lemma lem3709041 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3709042 {A B : Type'} (f : A -> B) : (term680 A B f) = (term689 A B f).
Proof. exact (MK_COMB (@lem3709041 A) (@lem3709040 A B f)). Qed.
Lemma lem3709043 {A B : Type'} : (term681 A B) = (term690 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3709042 A B f)). Qed.
Lemma lem3709044 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3709045 {A B : Type'} : (term682 A B) = (term691 A B).
Proof. exact (MK_COMB (@lem3709044 A B) (@lem3709043 A B)). Qed.
Lemma lem3709046 {A B : Type'} : (term534 A B) = (term691 A B).
Proof. exact (TRANS (@lem3709004 A B) (@lem3709045 A B)). Qed.
Lemma lem3709047 {A B : Type'} (s'' : type525 A B) (h1 : term638 A B s'') : term691 A B.
Proof. exact (EQ_MP (@lem3709046 A B) (@lem3708348 A B s'' h1)). Qed.
Lemma lem3709229 {B : Type'} (_42677 : B -> Prop) (h1 : term15 B) : term692 B _42677.
Proof. exact (@lem3708374 B h1 _42677). Qed.
Lemma lem3709230 {B : Type'} (_42677 : B -> Prop) : (term692 B _42677) = (@SUBSET B _42677 _42677).
Proof. exact (eq_refl (term692 B _42677)). Qed.
Lemma lem3709283 {A B : Type'} (_42695 : A -> B) (s'' : type525 A B) (h1 : term638 A B s'') : term693 A B s'' _42695.
Proof. exact (@lem3708656 A B s'' h1 _42695). Qed.
Lemma lem3709284 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) : (term693 A B s'' _42695) = (term658 A B s'' _42695).
Proof. exact (eq_refl (term693 A B s'' _42695)). Qed.
Lemma lem3709285 {A B : Type'} (_42695 : A -> B) (s'' : type525 A B) (h1 : term638 A B s'') : term658 A B s'' _42695.
Proof. exact (EQ_MP (@lem3709284 A B s'' _42695) (@lem3709283 A B _42695 s'' h1)). Qed.
Lemma lem3709286 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term694 A B s'' _42695 _42696.
Proof. exact (@lem3709285 A B _42695 s'' h1 _42696). Qed.
Lemma lem3709287 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) : (term694 A B s'' _42695 _42696) = (term656 A B s'' _42695 _42696).
Proof. exact (eq_refl (term694 A B s'' _42695 _42696)). Qed.
Lemma lem3709288 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term656 A B s'' _42695 _42696.
Proof. exact (EQ_MP (@lem3709287 A B s'' _42695 _42696) (@lem3709286 A B _42695 _42696 s'' h1)). Qed.
Lemma lem3709289 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term695 A B s'' _42695 _42696 _42697.
Proof. exact (@lem3709288 A B _42695 _42696 s'' h1 _42697). Qed.
Lemma lem3709290 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term695 A B s'' _42695 _42696 _42697) = (term654 A B s'' _42695 _42696 _42697).
Proof. exact (eq_refl (term695 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3709291 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term654 A B s'' _42695 _42696 _42697.
Proof. exact (EQ_MP (@lem3709290 A B s'' _42695 _42696 _42697) (@lem3709289 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3709313 {A B : Type'} (_42705 : A -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term696 A B s f _42705.
Proof. exact (@lem3708796 A B s f h1 _42705). Qed.
Lemma lem3709314 {A B : Type'} (s : A -> Prop) (f : A -> B) (_42705 : A -> Prop) : (term696 A B s f _42705) = (term84 A B s f _42705).
Proof. exact (eq_refl (term696 A B s f _42705)). Qed.
Lemma lem3709361 {A B : Type'} (_42721 : A -> B) (s'' : type525 A B) (h1 : term638 A B s'') : term697 A B _42721.
Proof. exact (@lem3709047 A B s'' h1 _42721). Qed.
Lemma lem3709362 {A B : Type'} (_42721 : A -> B) : (term697 A B _42721) = (term689 A B _42721).
Proof. exact (eq_refl (term697 A B _42721)). Qed.
Lemma lem3709363 {A B : Type'} (_42721 : A -> B) (s'' : type525 A B) (h1 : term638 A B s'') : term689 A B _42721.
Proof. exact (EQ_MP (@lem3709362 A B _42721) (@lem3709361 A B _42721 s'' h1)). Qed.
Lemma lem3709364 {A B : Type'} (_42721 : A -> B) (_42722 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term698 A B _42721 _42722.
Proof. exact (@lem3709363 A B _42721 s'' h1 _42722). Qed.
Lemma lem3709365 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) : (term698 A B _42721 _42722) = (term687 A B _42722 _42721).
Proof. exact (eq_refl (term698 A B _42721 _42722)). Qed.
Lemma lem3709366 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) (s'' : type525 A B) (h1 : term638 A B s'') : term687 A B _42722 _42721.
Proof. exact (EQ_MP (@lem3709365 A B _42722 _42721) (@lem3709364 A B _42721 _42722 s'' h1)). Qed.
Lemma lem3709367 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) (_42723 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term699 A B _42722 _42721 _42723.
Proof. exact (@lem3709366 A B _42722 _42721 s'' h1 _42723). Qed.
Lemma lem3709368 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) : (term699 A B _42722 _42721 _42723) = (term685 A B _42722 _42723 _42721).
Proof. exact (eq_refl (term699 A B _42722 _42721 _42723)). Qed.
Lemma lem3709369 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (s'' : type525 A B) (h1 : term638 A B s'') : term685 A B _42722 _42723 _42721.
Proof. exact (EQ_MP (@lem3709368 A B _42722 _42723 _42721) (@lem3709367 A B _42722 _42721 _42723 s'' h1)). Qed.
Lemma lem3709370 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term700 A B _42722 _42723 _42721 _42724.
Proof. exact (@lem3709369 A B _42722 _42723 _42721 s'' h1 _42724). Qed.
Lemma lem3709371 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term700 A B _42722 _42723 _42721 _42724) = (term683 A B _42722 _42723 _42721 _42724).
Proof. exact (eq_refl (term700 A B _42722 _42723 _42721 _42724)). Qed.
Lemma lem3709372 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term683 A B _42722 _42723 _42721 _42724.
Proof. exact (EQ_MP (@lem3709371 A B _42722 _42723 _42721 _42724) (@lem3709370 A B _42722 _42723 _42721 _42724 s'' h1)). Qed.
Lemma lem3709409 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term650 A B s'' _42695 _42696 _42697.
Proof. exact (proj2 (@lem3709291 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3709410 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term701 A B s'' _42695 _42696 _42697.
Proof. exact (proj1 (@lem3709291 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3709411 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term702 A B s'' _42695 _42696 _42697.
Proof. exact (proj2 (@lem3709409 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3709412 {A B : Type'} (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term703 A B s'' _42695 _42697 _42696.
Proof. exact (proj1 (@lem3709409 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3709472 {A B : Type'} (_42705 : A -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term84 A B s f _42705.
Proof. exact (EQ_MP (@lem3709314 A B s f _42705) (@lem3709313 A B _42705 s f h1)). Qed.
Lemma lem3709547 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term701 A B s'' _42695 _42696 _42697) = (term704 A B s'' _42695 _42696 _42697).
Proof. exact (@lem3703690 (term705 B _42697) (term706 A B _42697 _42695 _42696) (term647 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3709548 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term704 A B s'' _42695 _42696 _42697.
Proof. exact (EQ_MP (@lem3709547 A B s'' _42695 _42696 _42697) (@lem3709410 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3709559 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) : (term703 A B s'' _42695 _42697 _42696) = (term707 A B s'' _42695 _42697 _42696).
Proof. exact (@lem3703690 (term705 B _42697) (term706 A B _42697 _42695 _42696) (term651 A B s'' _42695 _42697 _42696)). Qed.
Lemma lem3709560 {A B : Type'} (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term707 A B s'' _42695 _42697 _42696.
Proof. exact (EQ_MP (@lem3709559 A B s'' _42695 _42697 _42696) (@lem3709412 A B _42695 _42697 _42696 s'' h1)). Qed.
Lemma lem3709571 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term702 A B s'' _42695 _42696 _42697) = (term708 A B s'' _42695 _42696 _42697).
Proof. exact (@lem3703690 (term705 B _42697) (term706 A B _42697 _42695 _42696) (_42697 = (term652 A B s'' _42695 _42696 _42697))). Qed.
Lemma lem3709572 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term708 A B s'' _42695 _42696 _42697.
Proof. exact (EQ_MP (@lem3709571 A B s'' _42695 _42696 _42697) (@lem3709411 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3709688 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term177 A B f s.
Proof. exact (proj1 (@lem3708352 A B s f t h1)). Qed.
Lemma lem3709808 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term709 A B _42722 _42723 _42721 _42724.
Proof. exact (proj1 (@lem3709372 A B _42722 _42723 _42721 _42724 s'' h1)). Qed.
Lemma lem3710071 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term76 A B f s.
Proof. exact (proj1 (@lem3708351 A B s f h1)). Qed.
Lemma lem3710072 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term710 A B f s.
Proof. exact (fun h0 : term177 A B f s => @lem3710071 A B s f h1). Qed.
Lemma lem3710074 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710075 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term710 A B f s) = (term76 A B f s).
Proof. exact (@lem3710074 (term76 A B f s)). Qed.
Lemma lem3710076 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term76 A B f s.
Proof. exact (EQ_MP (@lem3710075 A B f s) (@lem3710072 A B s f h1)). Qed.
Lemma lem3710078 {B : Type'} (_42677 : B -> Prop) (h1 : term15 B) : @SUBSET B _42677 _42677.
Proof. exact (EQ_MP (@lem3709230 B _42677) (@lem3709229 B _42677 h1)). Qed.
Lemma lem3710079 {B : Type'} (_42677 : B -> Prop) (h1 : term15 B) : @SUBSET B _42677 _42677.
Proof. exact (@lem3710078 B _42677 h1). Qed.
Lemma lem3710080 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term712 A B f s.
Proof. exact (@lem3710079 B (@IMAGE A B f s) h1). Qed.
Lemma lem3710081 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term713 A B f s.
Proof. exact (fun h0 : term714 A B f s => @lem3710080 A B f s h1). Qed.
Lemma lem3710083 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710084 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term713 A B f s) = (term712 A B f s).
Proof. exact (@lem3710083 (term712 A B f s)). Qed.
Lemma lem3710085 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term712 A B f s.
Proof. exact (EQ_MP (@lem3710084 A B f s) (@lem3710081 A B f s h1)). Qed.
Lemma lem3710101 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3710102 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term715 A B s'' _42695 _42696 _42697) = (term716 A B s'' _42697 _42695 _42696).
Proof. exact (@lem3710101 (term647 A B s'' _42695 _42696 _42697) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710108 {B : Type'} (_42697 : B -> Prop) : (term82 B _42697) = (term82 B _42697).
Proof. exact (eq_refl (term82 B _42697)). Qed.
Lemma lem3710109 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term704 A B s'' _42695 _42696 _42697) = (term717 A B s'' _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710108 B _42697) (@lem3710102 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710113 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3710114 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term717 A B s'' _42697 _42695 _42696) = (term718 A B s'' _42697 _42695 _42696).
Proof. exact (@lem3710113 (term647 A B s'' _42695 _42696 _42697) (term705 B _42697) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710130 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term704 A B s'' _42695 _42696 _42697) = (term718 A B s'' _42697 _42695 _42696).
Proof. exact (TRANS (@lem3710109 A B s'' _42697 _42695 _42696) (@lem3710114 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3710132 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term719 A B s'' _42695 _42696 _42697) = (term720 A B s'' _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710131) (@lem3710130 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710148 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term718 A B s'' _42697 _42695 _42696) = (term718 A B s'' _42697 _42695 _42696).
Proof. exact (eq_refl (term718 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710149 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term704 A B s'' _42695 _42696 _42697) = (term718 A B s'' _42697 _42695 _42696)) = ((term718 A B s'' _42697 _42695 _42696) = (term718 A B s'' _42697 _42695 _42696)).
Proof. exact (MK_COMB (@lem3710132 A B s'' _42697 _42695 _42696) (@lem3710148 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710151 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3710152 (x : Prop) : (x = x) = True.
Proof. exact (@lem3710151 Prop x). Qed.
Lemma lem3710153 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term718 A B s'' _42697 _42695 _42696) = (term718 A B s'' _42697 _42695 _42696)) = True.
Proof. exact (@lem3710152 (term718 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710154 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term704 A B s'' _42695 _42696 _42697) = (term718 A B s'' _42697 _42695 _42696)) = True.
Proof. exact (TRANS (@lem3710149 A B s'' _42697 _42695 _42696) (@lem3710153 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710155 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : True = ((term704 A B s'' _42695 _42696 _42697) = (term718 A B s'' _42697 _42695 _42696)).
Proof. exact (SYM (@lem3710154 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710156 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term704 A B s'' _42695 _42696 _42697) = (term718 A B s'' _42697 _42695 _42696).
Proof. exact (EQ_MP (@lem3710155 A B s'' _42697 _42695 _42696) (@lem0)). Qed.
Lemma lem3710157 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term718 A B s'' _42697 _42695 _42696.
Proof. exact (EQ_MP (@lem3710156 A B s'' _42697 _42695 _42696) (@lem3709548 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3710159 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3710160 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term718 A B s'' _42697 _42695 _42696) = (term722 A B s'' _42695 _42696 _42697).
Proof. exact (@lem3710159 (term443 A B _42697 _42695 _42696) (term647 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3710162 (a : Prop) (b : Prop) : (term723 a b) = (term724 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3710163 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term725 A B _42697 _42695 _42696) = (term726 A B _42697 _42695 _42696).
Proof. exact (@lem3710162 (term705 B _42697) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710165 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710166 {B : Type'} (_42697 : B -> Prop) : (term728 B _42697) = (@FINITE B _42697).
Proof. exact (@lem3710165 (@FINITE B _42697)). Qed.
Lemma lem3710167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3710168 {B : Type'} (_42697 : B -> Prop) : (term729 B _42697) = (term730 B _42697).
Proof. exact (MK_COMB (@lem3710167) (@lem3710166 B _42697)). Qed.
Lemma lem3710170 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710171 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term731 A B _42697 _42695 _42696) = (term444 A B _42697 _42695 _42696).
Proof. exact (@lem3710170 (term444 A B _42697 _42695 _42696)). Qed.
Lemma lem3710172 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term726 A B _42697 _42695 _42696) = (term57 A B _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710168 B _42697) (@lem3710171 A B _42697 _42695 _42696)). Qed.
Lemma lem3710173 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term725 A B _42697 _42695 _42696) = (term57 A B _42697 _42695 _42696).
Proof. exact (TRANS (@lem3710163 A B _42697 _42695 _42696) (@lem3710172 A B _42697 _42695 _42696)). Qed.
Lemma lem3710174 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3710175 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term732 A B _42697 _42695 _42696) = (term733 A B _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710174) (@lem3710173 A B _42697 _42695 _42696)). Qed.
Lemma lem3710176 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term647 A B s'' _42695 _42696 _42697) = (term647 A B s'' _42695 _42696 _42697).
Proof. exact (eq_refl (term647 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3710177 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term722 A B s'' _42695 _42696 _42697) = (term734 A B s'' _42695 _42696 _42697).
Proof. exact (MK_COMB (@lem3710175 A B _42697 _42695 _42696) (@lem3710176 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3710178 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term718 A B s'' _42697 _42695 _42696) = (term734 A B s'' _42695 _42696 _42697).
Proof. exact (TRANS (@lem3710160 A B s'' _42695 _42696 _42697) (@lem3710177 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3710180 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term100 A B s f) : term735 A B f s.
Proof. exact (conj (@lem3710076 A B s f h2) (@lem3710085 A B f s h1)). Qed.
Lemma lem3710182 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term734 A B s'' _42695 _42696 _42697.
Proof. exact (EQ_MP (@lem3710178 A B s'' _42695 _42696 _42697) (@lem3710157 A B _42697 _42695 _42696 s'' h1)). Qed.
Lemma lem3710183 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term734 A B s'' _42695 _42696 _42697.
Proof. exact (@lem3710182 A B _42695 _42696 _42697 s'' h1). Qed.
Lemma lem3710184 {A B : Type'} (f : A -> B) (s : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term736 A B s'' f s.
Proof. exact (@lem3710183 A B f s (@IMAGE A B f s) s'' h1). Qed.
Lemma lem3710187 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term737 A B s'' f s.
Proof. exact (@lem3710184 A B f s s'' h2 (@lem3710180 A B s f h1 h3)). Qed.
Lemma lem3710188 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term738 A B s'' f s.
Proof. exact (fun h0 : term739 A B s'' f s => @lem3710187 A B s'' s f h1 h2 h3). Qed.
Lemma lem3710190 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710191 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term738 A B s'' f s) = (term737 A B s'' f s).
Proof. exact (@lem3710190 (term737 A B s'' f s)). Qed.
Lemma lem3710192 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term737 A B s'' f s.
Proof. exact (EQ_MP (@lem3710191 A B s'' f s) (@lem3710188 A B s'' s f h1 h2 h3)). Qed.
Lemma lem3710194 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term76 A B f s.
Proof. exact (proj1 (@lem3708351 A B s f h1)). Qed.
Lemma lem3710195 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term710 A B f s.
Proof. exact (fun h0 : term177 A B f s => @lem3710194 A B s f h1). Qed.
Lemma lem3710197 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710198 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term710 A B f s) = (term76 A B f s).
Proof. exact (@lem3710197 (term76 A B f s)). Qed.
Lemma lem3710199 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term76 A B f s.
Proof. exact (EQ_MP (@lem3710198 A B f s) (@lem3710195 A B s f h1)). Qed.
Lemma lem3710201 {B : Type'} (_42677 : B -> Prop) (h1 : term15 B) : @SUBSET B _42677 _42677.
Proof. exact (EQ_MP (@lem3709230 B _42677) (@lem3709229 B _42677 h1)). Qed.
Lemma lem3710202 {B : Type'} (_42677 : B -> Prop) (h1 : term15 B) : @SUBSET B _42677 _42677.
Proof. exact (@lem3710201 B _42677 h1). Qed.
Lemma lem3710203 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term712 A B f s.
Proof. exact (@lem3710202 B (@IMAGE A B f s) h1). Qed.
Lemma lem3710204 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term713 A B f s.
Proof. exact (fun h0 : term714 A B f s => @lem3710203 A B f s h1). Qed.
Lemma lem3710206 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710207 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term713 A B f s) = (term712 A B f s).
Proof. exact (@lem3710206 (term712 A B f s)). Qed.
Lemma lem3710208 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term712 A B f s.
Proof. exact (EQ_MP (@lem3710207 A B f s) (@lem3710204 A B f s h1)). Qed.
Lemma lem3710224 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3710225 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term740 A B s'' _42695 _42697 _42696) = (term741 A B s'' _42697 _42695 _42696).
Proof. exact (@lem3710224 (term651 A B s'' _42695 _42697 _42696) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710231 {B : Type'} (_42697 : B -> Prop) : (term82 B _42697) = (term82 B _42697).
Proof. exact (eq_refl (term82 B _42697)). Qed.
Lemma lem3710232 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term707 A B s'' _42695 _42697 _42696) = (term742 A B s'' _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710231 B _42697) (@lem3710225 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710236 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3710237 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term742 A B s'' _42697 _42695 _42696) = (term743 A B s'' _42697 _42695 _42696).
Proof. exact (@lem3710236 (term651 A B s'' _42695 _42697 _42696) (term705 B _42697) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710253 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term707 A B s'' _42695 _42697 _42696) = (term743 A B s'' _42697 _42695 _42696).
Proof. exact (TRANS (@lem3710232 A B s'' _42697 _42695 _42696) (@lem3710237 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3710255 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term744 A B s'' _42695 _42697 _42696) = (term745 A B s'' _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710254) (@lem3710253 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710271 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term743 A B s'' _42697 _42695 _42696) = (term743 A B s'' _42697 _42695 _42696).
Proof. exact (eq_refl (term743 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710272 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term707 A B s'' _42695 _42697 _42696) = (term743 A B s'' _42697 _42695 _42696)) = ((term743 A B s'' _42697 _42695 _42696) = (term743 A B s'' _42697 _42695 _42696)).
Proof. exact (MK_COMB (@lem3710255 A B s'' _42697 _42695 _42696) (@lem3710271 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710274 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3710275 (x : Prop) : (x = x) = True.
Proof. exact (@lem3710274 Prop x). Qed.
Lemma lem3710276 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term743 A B s'' _42697 _42695 _42696) = (term743 A B s'' _42697 _42695 _42696)) = True.
Proof. exact (@lem3710275 (term743 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710277 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term707 A B s'' _42695 _42697 _42696) = (term743 A B s'' _42697 _42695 _42696)) = True.
Proof. exact (TRANS (@lem3710272 A B s'' _42697 _42695 _42696) (@lem3710276 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710278 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : True = ((term707 A B s'' _42695 _42697 _42696) = (term743 A B s'' _42697 _42695 _42696)).
Proof. exact (SYM (@lem3710277 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710279 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term707 A B s'' _42695 _42697 _42696) = (term743 A B s'' _42697 _42695 _42696).
Proof. exact (EQ_MP (@lem3710278 A B s'' _42697 _42695 _42696) (@lem0)). Qed.
Lemma lem3710280 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term743 A B s'' _42697 _42695 _42696.
Proof. exact (EQ_MP (@lem3710279 A B s'' _42697 _42695 _42696) (@lem3709560 A B _42695 _42697 _42696 s'' h1)). Qed.
Lemma lem3710282 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3710283 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) : (term743 A B s'' _42697 _42695 _42696) = (term746 A B s'' _42695 _42697 _42696).
Proof. exact (@lem3710282 (term443 A B _42697 _42695 _42696) (term651 A B s'' _42695 _42697 _42696)). Qed.
Lemma lem3710285 (a : Prop) (b : Prop) : (term723 a b) = (term724 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3710286 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term725 A B _42697 _42695 _42696) = (term726 A B _42697 _42695 _42696).
Proof. exact (@lem3710285 (term705 B _42697) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710288 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710289 {B : Type'} (_42697 : B -> Prop) : (term728 B _42697) = (@FINITE B _42697).
Proof. exact (@lem3710288 (@FINITE B _42697)). Qed.
Lemma lem3710290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3710291 {B : Type'} (_42697 : B -> Prop) : (term729 B _42697) = (term730 B _42697).
Proof. exact (MK_COMB (@lem3710290) (@lem3710289 B _42697)). Qed.
Lemma lem3710293 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710294 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term731 A B _42697 _42695 _42696) = (term444 A B _42697 _42695 _42696).
Proof. exact (@lem3710293 (term444 A B _42697 _42695 _42696)). Qed.
Lemma lem3710295 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term726 A B _42697 _42695 _42696) = (term57 A B _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710291 B _42697) (@lem3710294 A B _42697 _42695 _42696)). Qed.
Lemma lem3710296 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term725 A B _42697 _42695 _42696) = (term57 A B _42697 _42695 _42696).
Proof. exact (TRANS (@lem3710286 A B _42697 _42695 _42696) (@lem3710295 A B _42697 _42695 _42696)). Qed.
Lemma lem3710297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3710298 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term732 A B _42697 _42695 _42696) = (term733 A B _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710297) (@lem3710296 A B _42697 _42695 _42696)). Qed.
Lemma lem3710299 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) : (term651 A B s'' _42695 _42697 _42696) = (term651 A B s'' _42695 _42697 _42696).
Proof. exact (eq_refl (term651 A B s'' _42695 _42697 _42696)). Qed.
Lemma lem3710300 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) : (term746 A B s'' _42695 _42697 _42696) = (term747 A B s'' _42695 _42697 _42696).
Proof. exact (MK_COMB (@lem3710298 A B _42697 _42695 _42696) (@lem3710299 A B s'' _42695 _42697 _42696)). Qed.
Lemma lem3710301 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) : (term743 A B s'' _42697 _42695 _42696) = (term747 A B s'' _42695 _42697 _42696).
Proof. exact (TRANS (@lem3710283 A B s'' _42695 _42697 _42696) (@lem3710300 A B s'' _42695 _42697 _42696)). Qed.
Lemma lem3710303 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term100 A B s f) : term735 A B f s.
Proof. exact (conj (@lem3710199 A B s f h2) (@lem3710208 A B f s h1)). Qed.
Lemma lem3710305 {A B : Type'} (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term747 A B s'' _42695 _42697 _42696.
Proof. exact (EQ_MP (@lem3710301 A B s'' _42695 _42697 _42696) (@lem3710280 A B _42697 _42695 _42696 s'' h1)). Qed.
Lemma lem3710306 {A B : Type'} (_42695 : A -> B) (_42697 : B -> Prop) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term747 A B s'' _42695 _42697 _42696.
Proof. exact (@lem3710305 A B _42695 _42697 _42696 s'' h1). Qed.
Lemma lem3710307 {A B : Type'} (f : A -> B) (s : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term748 A B s'' f s.
Proof. exact (@lem3710306 A B f (@IMAGE A B f s) s s'' h1). Qed.
Lemma lem3710310 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term749 A B s'' f s.
Proof. exact (@lem3710307 A B f s s'' h2 (@lem3710303 A B s f h1 h3)). Qed.
Lemma lem3710311 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term750 A B s'' f s.
Proof. exact (fun h0 : term751 A B s'' f s => @lem3710310 A B s'' s f h1 h2 h3). Qed.
Lemma lem3710313 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710314 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term750 A B s'' f s) = (term749 A B s'' f s).
Proof. exact (@lem3710313 (term749 A B s'' f s)). Qed.
Lemma lem3710315 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term749 A B s'' f s.
Proof. exact (EQ_MP (@lem3710314 A B s'' f s) (@lem3710311 A B s'' s f h1 h2 h3)). Qed.
Lemma lem3710317 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term76 A B f s.
Proof. exact (proj1 (@lem3708351 A B s f h1)). Qed.
Lemma lem3710318 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term710 A B f s.
Proof. exact (fun h0 : term177 A B f s => @lem3710317 A B s f h1). Qed.
Lemma lem3710320 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710321 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term710 A B f s) = (term76 A B f s).
Proof. exact (@lem3710320 (term76 A B f s)). Qed.
Lemma lem3710322 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term76 A B f s.
Proof. exact (EQ_MP (@lem3710321 A B f s) (@lem3710318 A B s f h1)). Qed.
Lemma lem3710324 {B : Type'} (_42677 : B -> Prop) (h1 : term15 B) : @SUBSET B _42677 _42677.
Proof. exact (EQ_MP (@lem3709230 B _42677) (@lem3709229 B _42677 h1)). Qed.
Lemma lem3710325 {B : Type'} (_42677 : B -> Prop) (h1 : term15 B) : @SUBSET B _42677 _42677.
Proof. exact (@lem3710324 B _42677 h1). Qed.
Lemma lem3710326 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term712 A B f s.
Proof. exact (@lem3710325 B (@IMAGE A B f s) h1). Qed.
Lemma lem3710327 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term713 A B f s.
Proof. exact (fun h0 : term714 A B f s => @lem3710326 A B f s h1). Qed.
Lemma lem3710329 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710330 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term713 A B f s) = (term712 A B f s).
Proof. exact (@lem3710329 (term712 A B f s)). Qed.
Lemma lem3710331 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term15 B) : term712 A B f s.
Proof. exact (EQ_MP (@lem3710330 A B f s) (@lem3710327 A B f s h1)). Qed.
Lemma lem3710347 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3710348 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term752 A B s'' _42695 _42696 _42697) = (term753 A B s'' _42697 _42695 _42696).
Proof. exact (@lem3710347 (_42697 = (term652 A B s'' _42695 _42696 _42697)) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710356 {B : Type'} (_42697 : B -> Prop) : (term82 B _42697) = (term82 B _42697).
Proof. exact (eq_refl (term82 B _42697)). Qed.
Lemma lem3710357 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term708 A B s'' _42695 _42696 _42697) = (term754 A B s'' _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710356 B _42697) (@lem3710348 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710361 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3710362 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term754 A B s'' _42697 _42695 _42696) = (term755 A B s'' _42697 _42695 _42696).
Proof. exact (@lem3710361 (_42697 = (term652 A B s'' _42695 _42696 _42697)) (term705 B _42697) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710380 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term708 A B s'' _42695 _42696 _42697) = (term755 A B s'' _42697 _42695 _42696).
Proof. exact (TRANS (@lem3710357 A B s'' _42697 _42695 _42696) (@lem3710362 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3710382 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term756 A B s'' _42695 _42696 _42697) = (term757 A B s'' _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710381) (@lem3710380 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710400 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term755 A B s'' _42697 _42695 _42696) = (term755 A B s'' _42697 _42695 _42696).
Proof. exact (eq_refl (term755 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710401 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term708 A B s'' _42695 _42696 _42697) = (term755 A B s'' _42697 _42695 _42696)) = ((term755 A B s'' _42697 _42695 _42696) = (term755 A B s'' _42697 _42695 _42696)).
Proof. exact (MK_COMB (@lem3710382 A B s'' _42697 _42695 _42696) (@lem3710400 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710403 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3710404 (x : Prop) : (x = x) = True.
Proof. exact (@lem3710403 Prop x). Qed.
Lemma lem3710405 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term755 A B s'' _42697 _42695 _42696) = (term755 A B s'' _42697 _42695 _42696)) = True.
Proof. exact (@lem3710404 (term755 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710406 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : ((term708 A B s'' _42695 _42696 _42697) = (term755 A B s'' _42697 _42695 _42696)) = True.
Proof. exact (TRANS (@lem3710401 A B s'' _42697 _42695 _42696) (@lem3710405 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710407 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : True = ((term708 A B s'' _42695 _42696 _42697) = (term755 A B s'' _42697 _42695 _42696)).
Proof. exact (SYM (@lem3710406 A B s'' _42697 _42695 _42696)). Qed.
Lemma lem3710408 {A B : Type'} (s'' : type525 A B) (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term708 A B s'' _42695 _42696 _42697) = (term755 A B s'' _42697 _42695 _42696).
Proof. exact (EQ_MP (@lem3710407 A B s'' _42697 _42695 _42696) (@lem0)). Qed.
Lemma lem3710409 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term755 A B s'' _42697 _42695 _42696.
Proof. exact (EQ_MP (@lem3710408 A B s'' _42697 _42695 _42696) (@lem3709572 A B _42695 _42696 _42697 s'' h1)). Qed.
Lemma lem3710411 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3710412 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term755 A B s'' _42697 _42695 _42696) = (term758 A B s'' _42695 _42696 _42697).
Proof. exact (@lem3710411 (term443 A B _42697 _42695 _42696) (_42697 = (term652 A B s'' _42695 _42696 _42697))). Qed.
Lemma lem3710414 (a : Prop) (b : Prop) : (term723 a b) = (term724 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3710415 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term725 A B _42697 _42695 _42696) = (term726 A B _42697 _42695 _42696).
Proof. exact (@lem3710414 (term705 B _42697) (term706 A B _42697 _42695 _42696)). Qed.
Lemma lem3710417 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710418 {B : Type'} (_42697 : B -> Prop) : (term728 B _42697) = (@FINITE B _42697).
Proof. exact (@lem3710417 (@FINITE B _42697)). Qed.
Lemma lem3710419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3710420 {B : Type'} (_42697 : B -> Prop) : (term729 B _42697) = (term730 B _42697).
Proof. exact (MK_COMB (@lem3710419) (@lem3710418 B _42697)). Qed.
Lemma lem3710422 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710423 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term731 A B _42697 _42695 _42696) = (term444 A B _42697 _42695 _42696).
Proof. exact (@lem3710422 (term444 A B _42697 _42695 _42696)). Qed.
Lemma lem3710424 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term726 A B _42697 _42695 _42696) = (term57 A B _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710420 B _42697) (@lem3710423 A B _42697 _42695 _42696)). Qed.
Lemma lem3710425 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term725 A B _42697 _42695 _42696) = (term57 A B _42697 _42695 _42696).
Proof. exact (TRANS (@lem3710415 A B _42697 _42695 _42696) (@lem3710424 A B _42697 _42695 _42696)). Qed.
Lemma lem3710426 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3710427 {A B : Type'} (_42697 : B -> Prop) (_42695 : A -> B) (_42696 : A -> Prop) : (term732 A B _42697 _42695 _42696) = (term733 A B _42697 _42695 _42696).
Proof. exact (MK_COMB (@lem3710426) (@lem3710425 A B _42697 _42695 _42696)). Qed.
Lemma lem3710428 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (_42697 = (term652 A B s'' _42695 _42696 _42697)) = (_42697 = (term652 A B s'' _42695 _42696 _42697)).
Proof. exact (eq_refl (_42697 = (term652 A B s'' _42695 _42696 _42697))). Qed.
Lemma lem3710429 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term758 A B s'' _42695 _42696 _42697) = (term759 A B s'' _42695 _42696 _42697).
Proof. exact (MK_COMB (@lem3710427 A B _42697 _42695 _42696) (@lem3710428 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3710430 {A B : Type'} (s'' : type525 A B) (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) : (term755 A B s'' _42697 _42695 _42696) = (term759 A B s'' _42695 _42696 _42697).
Proof. exact (TRANS (@lem3710412 A B s'' _42695 _42696 _42697) (@lem3710429 A B s'' _42695 _42696 _42697)). Qed.
Lemma lem3710432 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term100 A B s f) : term735 A B f s.
Proof. exact (conj (@lem3710322 A B s f h2) (@lem3710331 A B f s h1)). Qed.
Lemma lem3710434 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term759 A B s'' _42695 _42696 _42697.
Proof. exact (EQ_MP (@lem3710430 A B s'' _42695 _42696 _42697) (@lem3710409 A B _42697 _42695 _42696 s'' h1)). Qed.
Lemma lem3710435 {A B : Type'} (_42695 : A -> B) (_42696 : A -> Prop) (_42697 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term759 A B s'' _42695 _42696 _42697.
Proof. exact (@lem3710434 A B _42695 _42696 _42697 s'' h1). Qed.
Lemma lem3710436 {A B : Type'} (f : A -> B) (s : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term760 A B s'' f s.
Proof. exact (@lem3710435 A B f s (@IMAGE A B f s) s'' h1). Qed.
Lemma lem3710439 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : (@IMAGE A B f s) = (term761 A B s'' f s).
Proof. exact (@lem3710436 A B f s s'' h2 (@lem3710432 A B s f h1 h3)). Qed.
Lemma lem3710440 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term762 A B s'' f s.
Proof. exact (fun h0 : term763 A B s'' f s => @lem3710439 A B s'' s f h1 h2 h3). Qed.
Lemma lem3710442 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710443 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term762 A B s'' f s) = ((@IMAGE A B f s) = (term761 A B s'' f s)).
Proof. exact (@lem3710442 ((@IMAGE A B f s) = (term761 A B s'' f s))). Qed.
Lemma lem3710444 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : (@IMAGE A B f s) = (term761 A B s'' f s).
Proof. exact (EQ_MP (@lem3710443 A B s'' f s) (@lem3710440 A B s'' s f h1 h2 h3)). Qed.
Lemma lem3710446 (a : Prop) (b : Prop) : (term764 a b) = (term765 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3710447 {A B : Type'} (s : A -> Prop) (f : A -> B) (_42705 : A -> Prop) : (term81 A B s f _42705) = (term80 A B s f _42705).
Proof. exact (@lem3710446 (@SUBSET A _42705 s) ((@IMAGE A B f s) = (@IMAGE A B f _42705))). Qed.
Lemma lem3710448 {A : Type'} (_42705 : A -> Prop) : (term82 A _42705) = (term82 A _42705).
Proof. exact (eq_refl (term82 A _42705)). Qed.
Lemma lem3710449 {A B : Type'} (s : A -> Prop) (f : A -> B) (_42705 : A -> Prop) : (term84 A B s f _42705) = (term83 A B s f _42705).
Proof. exact (MK_COMB (@lem3710448 A _42705) (@lem3710447 A B s f _42705)). Qed.
Lemma lem3710451 (a : Prop) (b : Prop) : (term764 a b) = (term765 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3710452 {A B : Type'} (s : A -> Prop) (f : A -> B) (_42705 : A -> Prop) : (term83 A B s f _42705) = (term85 A B s f _42705).
Proof. exact (@lem3710451 (@FINITE A _42705) (term86 A B s f _42705)). Qed.
Lemma lem3710453 {A B : Type'} (s : A -> Prop) (f : A -> B) (_42705 : A -> Prop) : (term84 A B s f _42705) = (term85 A B s f _42705).
Proof. exact (TRANS (@lem3710449 A B s f _42705) (@lem3710452 A B s f _42705)). Qed.
Lemma lem3710455 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3710456 {A B : Type'} (s : A -> Prop) (f : A -> B) (_42705 : A -> Prop) : (term85 A B s f _42705) = (term766 A B s f _42705).
Proof. exact (@lem3710455 (term72 A B s f _42705)). Qed.
Lemma lem3710457 {A B : Type'} (s : A -> Prop) (f : A -> B) (_42705 : A -> Prop) : (term84 A B s f _42705) = (term766 A B s f _42705).
Proof. exact (TRANS (@lem3710453 A B s f _42705) (@lem3710456 A B s f _42705)). Qed.
Lemma lem3710459 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term767 A B s'' f s.
Proof. exact (conj (@lem3710315 A B s'' s f h1 h2 h3) (@lem3710444 A B s'' s f h1 h2 h3)). Qed.
Lemma lem3710460 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term768 A B s'' f s.
Proof. exact (conj (@lem3710192 A B s'' s f h1 h2 h3) (@lem3710459 A B s'' s f h1 h2 h3)). Qed.
Lemma lem3710462 {A B : Type'} (_42705 : A -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term766 A B s f _42705.
Proof. exact (EQ_MP (@lem3710457 A B s f _42705) (@lem3709472 A B _42705 s f h1)). Qed.
Lemma lem3710463 {A B : Type'} (_42705 : A -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term766 A B s f _42705.
Proof. exact (@lem3710462 A B _42705 s f h1). Qed.
Lemma lem3710464 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term100 A B s f) : term769 A B s'' f s.
Proof. exact (@lem3710463 A B (term770 A B s'' f s) s f h1). Qed.
Lemma lem3710467 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : False.
Proof. exact (@lem3710464 A B s'' s f h3 (@lem3710460 A B s'' s f h1 h2 h3)). Qed.
Lemma lem3710468 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : term771.
Proof. exact (fun h0 : ~ False => @lem3710467 A B s'' s f h1 h2 h3). Qed.
Lemma lem3710470 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710471 : term771 = False.
Proof. exact (@lem3710470 False). Qed.
Lemma lem3710472 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : False.
Proof. exact (EQ_MP (@lem3710471) (@lem3710468 A B s'' s f h1 h2 h3)). Qed.
Lemma lem3710657 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : @FINITE A t.
Proof. exact (proj1 (@lem3708355 A B s f t h1)). Qed.
Lemma lem3710658 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term772 A t.
Proof. exact (fun h0 : term705 A t => @lem3710657 A B s f t h1). Qed.
Lemma lem3710660 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710661 {A : Type'} (t : A -> Prop) : (term772 A t) = (@FINITE A t).
Proof. exact (@lem3710660 (@FINITE A t)). Qed.
Lemma lem3710662 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : @FINITE A t.
Proof. exact (EQ_MP (@lem3710661 A t) (@lem3710658 A B s f t h1)). Qed.
Lemma lem3710664 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : @SUBSET A t s.
Proof. exact (proj1 (@lem3708357 A B s f t h1)). Qed.
Lemma lem3710665 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term773 A t s.
Proof. exact (fun h0 : term774 A t s => @lem3710664 A B s f t h1). Qed.
Lemma lem3710667 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710668 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term773 A t s) = (@SUBSET A t s).
Proof. exact (@lem3710667 (@SUBSET A t s)). Qed.
Lemma lem3710669 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : @SUBSET A t s.
Proof. exact (EQ_MP (@lem3710668 A t s) (@lem3710665 A B s f t h1)). Qed.
Lemma lem3710671 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : (@IMAGE A B f s) = (@IMAGE A B f t).
Proof. exact (proj2 (@lem3708357 A B s f t h1)). Qed.
Lemma lem3710672 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term775 A B s f t.
Proof. exact (fun h0 : term776 A B s f t => @lem3710671 A B s f t h1). Qed.
Lemma lem3710674 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710675 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term775 A B s f t) = ((@IMAGE A B f s) = (@IMAGE A B f t)).
Proof. exact (@lem3710674 ((@IMAGE A B f s) = (@IMAGE A B f t))). Qed.
Lemma lem3710676 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : (@IMAGE A B f s) = (@IMAGE A B f t).
Proof. exact (EQ_MP (@lem3710675 A B s f t) (@lem3710672 A B s f t h1)). Qed.
Lemma lem3710678 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3710679 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (_42723 : B -> Prop) : (term709 A B _42722 _42723 _42721 _42724) = (term777 A B _42722 _42721 _42724 _42723).
Proof. exact (@lem3710678 (term448 A B _42722 _42723 _42721 _42724) (@FINITE B _42723)). Qed.
Lemma lem3710681 (a : Prop) (b : Prop) : (term723 a b) = (term724 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3710682 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term778 A B _42722 _42723 _42721 _42724) = (term779 A B _42722 _42723 _42721 _42724).
Proof. exact (@lem3710681 (term705 A _42724) (term446 A B _42722 _42723 _42721 _42724)). Qed.
Lemma lem3710684 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710685 {A : Type'} (_42724 : A -> Prop) : (term728 A _42724) = (@FINITE A _42724).
Proof. exact (@lem3710684 (@FINITE A _42724)). Qed.
Lemma lem3710686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3710687 {A : Type'} (_42724 : A -> Prop) : (term729 A _42724) = (term730 A _42724).
Proof. exact (MK_COMB (@lem3710686) (@lem3710685 A _42724)). Qed.
Lemma lem3710689 (a : Prop) (b : Prop) : (term723 a b) = (term724 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3710690 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term780 A B _42722 _42723 _42721 _42724) = (term781 A B _42722 _42723 _42721 _42724).
Proof. exact (@lem3710689 (term774 A _42724 _42722) (term782 A B _42723 _42721 _42724)). Qed.
Lemma lem3710692 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710693 {A : Type'} (_42724 : A -> Prop) (_42722 : A -> Prop) : (term783 A _42724 _42722) = (@SUBSET A _42724 _42722).
Proof. exact (@lem3710692 (@SUBSET A _42724 _42722)). Qed.
Lemma lem3710694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3710695 {A : Type'} (_42724 : A -> Prop) (_42722 : A -> Prop) : (term784 A _42724 _42722) = (term785 A _42724 _42722).
Proof. exact (MK_COMB (@lem3710694) (@lem3710693 A _42724 _42722)). Qed.
Lemma lem3710697 (a : Prop) : (term727 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3710698 {A B : Type'} (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term786 A B _42723 _42721 _42724) = (_42723 = (@IMAGE A B _42721 _42724)).
Proof. exact (@lem3710697 (_42723 = (@IMAGE A B _42721 _42724))). Qed.
Lemma lem3710699 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term781 A B _42722 _42723 _42721 _42724) = (term450 A B _42722 _42723 _42721 _42724).
Proof. exact (MK_COMB (@lem3710695 A _42724 _42722) (@lem3710698 A B _42723 _42721 _42724)). Qed.
Lemma lem3710700 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term780 A B _42722 _42723 _42721 _42724) = (term450 A B _42722 _42723 _42721 _42724).
Proof. exact (TRANS (@lem3710690 A B _42722 _42723 _42721 _42724) (@lem3710699 A B _42722 _42723 _42721 _42724)). Qed.
Lemma lem3710701 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term779 A B _42722 _42723 _42721 _42724) = (term53 A B _42722 _42723 _42721 _42724).
Proof. exact (MK_COMB (@lem3710687 A _42724) (@lem3710700 A B _42722 _42723 _42721 _42724)). Qed.
Lemma lem3710702 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term778 A B _42722 _42723 _42721 _42724) = (term53 A B _42722 _42723 _42721 _42724).
Proof. exact (TRANS (@lem3710682 A B _42722 _42723 _42721 _42724) (@lem3710701 A B _42722 _42723 _42721 _42724)). Qed.
Lemma lem3710703 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3710704 {A B : Type'} (_42722 : A -> Prop) (_42723 : B -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) : (term787 A B _42722 _42723 _42721 _42724) = (term788 A B _42722 _42723 _42721 _42724).
Proof. exact (MK_COMB (@lem3710703) (@lem3710702 A B _42722 _42723 _42721 _42724)). Qed.
Lemma lem3710705 {B : Type'} (_42723 : B -> Prop) : (@FINITE B _42723) = (@FINITE B _42723).
Proof. exact (eq_refl (@FINITE B _42723)). Qed.
Lemma lem3710706 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (_42723 : B -> Prop) : (term777 A B _42722 _42721 _42724 _42723) = (term789 A B _42722 _42721 _42724 _42723).
Proof. exact (MK_COMB (@lem3710704 A B _42722 _42723 _42721 _42724) (@lem3710705 B _42723)). Qed.
Lemma lem3710707 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (_42723 : B -> Prop) : (term709 A B _42722 _42723 _42721 _42724) = (term789 A B _42722 _42721 _42724 _42723).
Proof. exact (TRANS (@lem3710679 A B _42722 _42721 _42724 _42723) (@lem3710706 A B _42722 _42721 _42724 _42723)). Qed.
Lemma lem3710709 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term86 A B s f t.
Proof. exact (conj (@lem3710669 A B s f t h1) (@lem3710676 A B s f t h1)). Qed.
Lemma lem3710710 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term72 A B s f t.
Proof. exact (conj (@lem3710662 A B s f t h1) (@lem3710709 A B s f t h1)). Qed.
Lemma lem3710712 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (_42723 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term789 A B _42722 _42721 _42724 _42723.
Proof. exact (EQ_MP (@lem3710707 A B _42722 _42721 _42724 _42723) (@lem3709808 A B _42722 _42723 _42721 _42724 s'' h1)). Qed.
Lemma lem3710713 {A B : Type'} (_42722 : A -> Prop) (_42721 : A -> B) (_42724 : A -> Prop) (_42723 : B -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term789 A B _42722 _42721 _42724 _42723.
Proof. exact (@lem3710712 A B _42722 _42721 _42724 _42723 s'' h1). Qed.
Lemma lem3710714 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (s'' : type525 A B) (h1 : term638 A B s'') : term790 A B t f s.
Proof. exact (@lem3710713 A B s f t (@IMAGE A B f s) s'' h1). Qed.
Lemma lem3710717 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term638 A B s'') (h2 : term183 A B s f t) : term76 A B f s.
Proof. exact (@lem3710714 A B t f s s'' h1 (@lem3710710 A B s f t h2)). Qed.
Lemma lem3710718 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term638 A B s'') (h2 : term183 A B s f t) : term710 A B f s.
Proof. exact (fun h0 : term177 A B f s => @lem3710717 A B s'' s f t h1 h2). Qed.
Lemma lem3710720 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710721 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term710 A B f s) = (term76 A B f s).
Proof. exact (@lem3710720 (term76 A B f s)). Qed.
Lemma lem3710722 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term638 A B s'') (h2 : term183 A B s f t) : term76 A B f s.
Proof. exact (EQ_MP (@lem3710721 A B f s) (@lem3710718 A B s'' s f t h1 h2)). Qed.
Lemma lem3710725 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3710727 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term177 A B f s) = (term791 A B f s).
Proof. exact (@lem3710725 (term76 A B f s)). Qed.
Lemma lem3710730 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term183 A B s f t) : term791 A B f s.
Proof. exact (EQ_MP (@lem3710727 A B f s) (@lem3709688 A B s f t h1)). Qed.
Lemma lem3710733 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term638 A B s'') (h2 : term183 A B s f t) : False.
Proof. exact (@lem3710730 A B s f t h2 (@lem3710722 A B s'' s f t h1 h2)). Qed.
Lemma lem3710734 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term638 A B s'') (h2 : term183 A B s f t) : term771.
Proof. exact (fun h0 : ~ False => @lem3710733 A B s'' s f t h1 h2). Qed.
Lemma lem3710736 (p : Prop) : (term711 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3710737 : term771 = False.
Proof. exact (@lem3710736 False). Qed.
Lemma lem3710738 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term638 A B s'') (h2 : term183 A B s f t) : False.
Proof. exact (EQ_MP (@lem3710737) (@lem3710734 A B s'' s f t h1 h2)). Qed.
Lemma lem3710739 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : (term15 B) = False.
Proof. exact (prop_ext (fun h4 : term15 B => @lem3710472 A B s'' s f h1 h2 h3) (fun h4 : False => @lem3708374 B h1)). Qed.
Lemma lem3710740 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term100 A B s f) : False.
Proof. exact (EQ_MP (@lem3710739 A B s'' s f h1 h2 h3) (@lem3708374 B h1)). Qed.
Lemma lem3710741 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term228 A B s f t) : False.
Proof. exact (or_elim (@lem3708344 A B s f t h3) (fun h0 : term100 A B s f => @lem3710740 A B s'' s f h1 h2 h0) (fun h0 : term183 A B s f t => @lem3710738 A B s'' s f t h2 h0)). Qed.
Lemma lem3710742 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term228 A B s f t) : (term228 A B s f t) = False.
Proof. exact (prop_ext (fun h4 : term228 A B s f t => @lem3710741 A B s'' s f t h1 h2 h3) (fun h4 : False => @lem3708344 A B s f t h3)). Qed.
Lemma lem3710743 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term228 A B s f t) : False.
Proof. exact (EQ_MP (@lem3710742 A B s'' s f t h1 h2 h3) (@lem3708344 A B s f t h3)). Qed.
Lemma lem3710744 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term228 A B s f t) : (term638 A B s'') = False.
Proof. exact (prop_ext (fun h4 : term638 A B s'' => @lem3710743 A B s'' s f t h1 h2 h3) (fun h4 : False => @lem3708120 A B s'' h2)). Qed.
Lemma lem3710745 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term228 A B s f t) : False.
Proof. exact (EQ_MP (@lem3710744 A B s'' s f t h1 h2 h3) (@lem3708120 A B s'' h2)). Qed.
Lemma lem3710746 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term228 A B s f t) : (term15 B) = False.
Proof. exact (prop_ext (fun h4 : term15 B => @lem3710745 A B s'' s f t h1 h2 h3) (fun h4 : False => @lem3707784 B h1)). Qed.
Lemma lem3710747 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term15 B) (h2 : term638 A B s'') (h3 : term228 A B s f t) : False.
Proof. exact (EQ_MP (@lem3710746 A B s'' s f t h1 h2 h3) (@lem3707784 B h1)). Qed.
Lemma lem3710748 {A B : Type'} (s : A -> Prop) (f : A -> B) (s'' : type525 A B) (h1 : term15 B) (h2 : term231 A B s f) (h3 : term638 A B s'') : False.
Proof. exact (ex_elim (@lem3707765 A B s f h2) (fun t : A -> Prop => fun h0 : term230 A B s f t => @lem3710747 A B s'' s f t h1 h3 h0)). Qed.
Lemma lem3710749 {A B : Type'} (f : A -> B) (s'' : type525 A B) (h1 : term15 B) (h2 : term233 A B f) (h3 : term638 A B s'') : False.
Proof. exact (ex_elim (@lem3707764 A B f h2) (fun s : A -> Prop => fun h0 : term232 A B f s => @lem3710748 A B s f s'' h1 h0 h3)). Qed.
Lemma lem3710750 {A B : Type'} (s'' : type525 A B) (h1 : term15 B) (h2 : term10 A B) (h3 : term638 A B s'') : False.
Proof. exact (ex_elim (@lem3704968 A B h2) (fun f : A -> B => fun h0 : term234 A B f => @lem3710749 A B f s'' h1 h0 h3)). Qed.
Lemma lem3710751 {A B : Type'} (s'' : type525 A B) (h1 : term12 A) (h2 : term15 B) (h3 : term10 A B) (h4 : term638 A B s'') : False.
Proof. exact (ex_elim (@lem3706056 A h1) (fun s''' : type483 A => fun h0 : term440 A s''' => @lem3710750 A B s'' h2 h3 h4)). Qed.
Lemma lem3710752 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term15 B) (h4 : term10 A B) : False.
Proof. exact (ex_elim (@lem3706908 A B h2) (fun s'' : type525 A B => fun h0 : term640 A B s'' => @lem3710751 A B s'' h1 h3 h4 h0)). Qed.
Lemma lem3710753 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term12 B) (h4 : term15 B) (h5 : term10 A B) : False.
Proof. exact (ex_elim (@lem3707760 B h3) (fun s' : type483 B => fun h0 : term440 B s' => @lem3710752 A B h1 h2 h4 h5)). Qed.
Lemma lem3710754 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term12 B) (h4 : term15 B) (h5 : term10 A B) : (term15 B) = False.
Proof. exact (prop_ext (fun h6 : term15 B => @lem3710753 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem3704994 B h4)). Qed.
Lemma lem3710755 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term12 B) (h4 : term15 B) (h5 : term10 A B) : False.
Proof. exact (EQ_MP (@lem3710754 A B h1 h2 h3 h4 h5) (@lem3704994 B h4)). Qed.
Lemma lem3710756 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term15 B) (h4 : term10 A B) : term20 B.
Proof. exact (fun h0 : term12 B => @lem3710755 A B h1 h2 h0 h3 h4). Qed.
Lemma lem3710757 {B : Type'} : (term20 B) = (term21 B).
Proof. exact (@lem69 (term12 B)). Qed.
Lemma lem3710758 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term15 B) (h4 : term10 A B) : term21 B.
Proof. exact (EQ_MP (@lem3710757 B) (@lem3710756 A B h1 h2 h3 h4)). Qed.
Lemma lem3710759 {A B : Type'} (h1 : term12 A) (h2 : term15 B) (h3 : term10 A B) : term24 A B.
Proof. exact (fun h0 : term11 A B => @lem3710758 A B h1 h0 h2 h3). Qed.
Lemma lem3710760 {A B : Type'} (h1 : term15 B) (h2 : term10 A B) : term27 A B.
Proof. exact (fun h0 : term12 A => @lem3710759 A B h0 h1 h2). Qed.
Lemma lem3710761 {A B : Type'} (h1 : term15 B) (h2 : term10 A B) : term30 A B.
Proof. exact (fun h0 : term13 B => @lem3710760 A B h1 h2). Qed.
Lemma lem3710762 {A B : Type'} (h1 : term15 B) (h2 : term10 A B) : term33 A B.
Proof. exact (fun h0 : term14 A B => @lem3710761 A B h1 h2). Qed.
Lemma lem3710763 {A B : Type'} (h1 : term15 B) (h2 : term10 A B) : term35 A B.
Proof. exact (fun h0 : term13 A => @lem3710762 A B h1 h2). Qed.
Lemma lem3710764 {A B : Type'} (h1 : term10 A B) : term38 A B.
Proof. exact (fun h0 : term15 B => @lem3710763 A B h0 h1). Qed.
Lemma lem3710765 {A B : Type'} (h1 : term10 A B) : term40 A B.
Proof. exact (fun h0 : term15 A => @lem3710764 A B h1). Qed.
Lemma lem3710766 {A B : Type'} : term42 A B.
Proof. exact (fun h0 : term10 A B => @lem3710765 A B h0). Qed.
Lemma lem3710767 {A B : Type'} : term16 A B.
Proof. exact (EQ_MP (@lem3704363 A B) (@lem3710766 A B)). Qed.
Lemma lem3710769 {A B : Type'} : term16 A B.
Proof. exact (@lem3703728 A B (@lem3710767 A B)). Qed.
Lemma lem3710770 {A B : Type'} (h1 : term10 A B) : term39 A B.
Proof. exact (@lem3710769 A B (@lem3703695 A B h1)). Qed.
Lemma lem3710771 {A B : Type'} (h1 : term10 A B) : term37 A B.
Proof. exact (@lem3710770 A B h1 (@lem3703711 A)). Qed.
Lemma lem3710772 {A B : Type'} (h1 : term10 A B) : term34 A B.
Proof. exact (@lem3710771 A B h1 (@lem3703712 B)). Qed.
Lemma lem3710773 {A B : Type'} (h1 : term10 A B) : term32 A B.
Proof. exact (@lem3710772 A B h1 (@lem3703707 A)). Qed.
Lemma lem3710774 {A B : Type'} (h1 : term10 A B) : term29 A B.
Proof. exact (@lem3710773 A B h1 (@lem3703705 A B)). Qed.
Lemma lem3710775 {A B : Type'} (h1 : term10 A B) : term26 A B.
Proof. exact (@lem3710774 A B h1 (@lem3703704 B)). Qed.
Lemma lem3710776 {A B : Type'} (h1 : term10 A B) : term23 A B.
Proof. exact (@lem3710775 A B h1 (@lem3703697 A)). Qed.
Lemma lem3710777 {A B : Type'} (h1 : term10 A B) : term20 B.
Proof. exact (@lem3710776 A B h1 (@lem3703696 A B)). Qed.
Lemma lem3710778 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (@lem3710777 A B h1 (@lem3703700 B)). Qed.
Lemma lem3710779 {A B : Type'} (h1 : term10 A B) : (term10 A B) = False.
Proof. exact (prop_ext (fun h2 : term10 A B => @lem3710778 A B h1) (fun h2 : False => @lem3703695 A B h1)). Qed.
Lemma lem3710780 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (EQ_MP (@lem3710779 A B h1) (@lem3703695 A B h1)). Qed.
Lemma lem3710781 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term10 A B => @lem3710780 A B h0). Qed.
Lemma lem3710782 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem3703694 A B) (@lem3710781 A B)). Qed.
