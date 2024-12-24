Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_2_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3322886 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3322887 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (s = t) = (term0 _86827 s t).
Proof. exact (@lem3322886 _86827 s t). Qed.
Lemma lem3322888 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : ((term1 _86827 s t) = (@UNION _86827 s t)) = (term2 _86827 s t).
Proof. exact (@lem3322887 _86827 (term1 _86827 s t) (@UNION _86827 s t)). Qed.
Lemma lem3322897 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term2 _86827 s t) = ((term1 _86827 s t) = (@UNION _86827 s t)).
Proof. exact (SYM (@lem3322888 _86827 s t)). Qed.
Lemma lem3322905 {A : Type'} (s : type686 A) (x : A) : (term3 A x s) = (term4 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3322906 {_86827 : Type'} (s : type686 _86827) (x : _86827) : (term3 _86827 x s) = (term4 _86827 s x).
Proof. exact (@lem3322905 _86827 s x). Qed.
Lemma lem3322907 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term5 _86827 x s t) = (term6 _86827 s t x).
Proof. exact (@lem3322906 _86827 (term7 _86827 s t) x). Qed.
Lemma lem3322915 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3322916 {_86827 : Type'} (y : _86827 -> Prop) (x : _86827 -> Prop) (s : type686 _86827) : (term10 _86827 x y s) = (term11 _86827 y x s).
Proof. exact (@lem3322915 (_86827 -> Prop) y x s). Qed.
Lemma lem3322917 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term12 _86827 t' s t) = (term13 _86827 s t' t).
Proof. exact (@lem3322916 _86827 s t' (@INSERT (_86827 -> Prop) t (@EMPTY (_86827 -> Prop)))). Qed.
Lemma lem3322923 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3322924 {_86827 : Type'} (y : _86827 -> Prop) (x : _86827 -> Prop) (s : type686 _86827) : (term10 _86827 x y s) = (term11 _86827 y x s).
Proof. exact (@lem3322923 (_86827 -> Prop) y x s). Qed.
Lemma lem3322925 {_86827 : Type'} (t : _86827 -> Prop) (t' : _86827 -> Prop) : (term14 _86827 t' t) = (term15 _86827 t t').
Proof. exact (@lem3322924 _86827 t t' (@EMPTY (_86827 -> Prop))). Qed.
Lemma lem3322931 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3322932 {_86827 : Type'} (x : _86827 -> Prop) : (@IN (_86827 -> Prop) x (@EMPTY (_86827 -> Prop))) = False.
Proof. exact (@lem3322931 (_86827 -> Prop) x). Qed.
Lemma lem3322933 {_86827 : Type'} (t' : _86827 -> Prop) : (@IN (_86827 -> Prop) t' (@EMPTY (_86827 -> Prop))) = False.
Proof. exact (@lem3322932 _86827 t'). Qed.
Lemma lem3322934 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term16 _86827 t' t) = (term16 _86827 t' t).
Proof. exact (eq_refl (term16 _86827 t' t)). Qed.
Lemma lem3322935 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term15 _86827 t t') = (term17 _86827 t' t).
Proof. exact (MK_COMB (@lem3322934 _86827 t' t) (@lem3322933 _86827 t')). Qed.
Lemma lem3322937 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3322938 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term17 _86827 t' t) = (t' = t).
Proof. exact (@lem3322937 (t' = t)). Qed.
Lemma lem3322941 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term15 _86827 t t') = (t' = t).
Proof. exact (TRANS (@lem3322935 _86827 t' t) (@lem3322938 _86827 t' t)). Qed.
Lemma lem3322942 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term14 _86827 t' t) = (t' = t).
Proof. exact (TRANS (@lem3322925 _86827 t t') (@lem3322941 _86827 t' t)). Qed.
Lemma lem3322943 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) : (term16 _86827 t' s) = (term16 _86827 t' s).
Proof. exact (eq_refl (term16 _86827 t' s)). Qed.
Lemma lem3322944 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term13 _86827 s t' t) = (term18 _86827 s t' t).
Proof. exact (MK_COMB (@lem3322943 _86827 t' s) (@lem3322942 _86827 t' t)). Qed.
Lemma lem3322947 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term12 _86827 t' s t) = (term18 _86827 s t' t).
Proof. exact (TRANS (@lem3322917 _86827 s t' t) (@lem3322944 _86827 s t' t)). Qed.
Lemma lem3322948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322949 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term19 _86827 t' s t) = (term20 _86827 s t' t).
Proof. exact (MK_COMB (@lem3322948) (@lem3322947 _86827 s t' t)). Qed.
Lemma lem3322951 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3322952 {_86827 : Type'} (P : _86827 -> Prop) (x : _86827) : (@IN _86827 x P) = (P x).
Proof. exact (@lem3322951 _86827 P x). Qed.
Lemma lem3322953 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (@IN _86827 x t') = (t' x).
Proof. exact (@lem3322952 _86827 t' x). Qed.
Lemma lem3322954 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term21 _86827 s t x t') = (term22 _86827 s t t' x).
Proof. exact (MK_COMB (@lem3322949 _86827 s t' t) (@lem3322953 _86827 t' x)). Qed.
Lemma lem3322957 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term23 _86827 s t x) = (term24 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3322954 _86827 s t t' x)). Qed.
Lemma lem3322958 {_86827 : Type'} : (@ex (_86827 -> Prop)) = (@ex (_86827 -> Prop)).
Proof. exact (eq_refl (@ex (_86827 -> Prop))). Qed.
Lemma lem3322959 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term6 _86827 s t x) = (term25 _86827 s t x).
Proof. exact (MK_COMB (@lem3322958 _86827) (@lem3322957 _86827 s t x)). Qed.
Lemma lem3322964 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term5 _86827 x s t) = (term25 _86827 s t x).
Proof. exact (TRANS (@lem3322907 _86827 s t x) (@lem3322959 _86827 s t x)). Qed.
Lemma lem3322965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3322966 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term26 _86827 x s t) = (term27 _86827 s t x).
Proof. exact (MK_COMB (@lem3322965) (@lem3322964 _86827 s t x)). Qed.
Lemma lem3322968 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3322969 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t : _86827 -> Prop) : (term28 _86827 x s t) = (term29 _86827 s x t).
Proof. exact (@lem3322968 _86827 s x t). Qed.
Lemma lem3322973 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3322974 {_86827 : Type'} (P : _86827 -> Prop) (x : _86827) : (@IN _86827 x P) = (P x).
Proof. exact (@lem3322973 _86827 P x). Qed.
Lemma lem3322975 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (@IN _86827 x s) = (s x).
Proof. exact (@lem3322974 _86827 s x). Qed.
Lemma lem3322976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3322977 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term30 _86827 x s) = (term31 _86827 s x).
Proof. exact (MK_COMB (@lem3322976) (@lem3322975 _86827 s x)). Qed.
Lemma lem3322979 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3322980 {_86827 : Type'} (P : _86827 -> Prop) (x : _86827) : (@IN _86827 x P) = (P x).
Proof. exact (@lem3322979 _86827 P x). Qed.
Lemma lem3322981 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (@IN _86827 x t) = (t x).
Proof. exact (@lem3322980 _86827 t x). Qed.
Lemma lem3322982 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term29 _86827 s x t) = (term32 _86827 s t x).
Proof. exact (MK_COMB (@lem3322977 _86827 s x) (@lem3322981 _86827 t x)). Qed.
Lemma lem3322985 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term28 _86827 x s t) = (term32 _86827 s t x).
Proof. exact (TRANS (@lem3322969 _86827 s x t) (@lem3322982 _86827 s t x)). Qed.
Lemma lem3322986 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term5 _86827 x s t) = (term28 _86827 x s t)) = ((term25 _86827 s t x) = (term32 _86827 s t x)).
Proof. exact (MK_COMB (@lem3322966 _86827 s t x) (@lem3322985 _86827 s t x)). Qed.
Lemma lem3322989 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term33 _86827 s t) = (term34 _86827 s t).
Proof. exact (fun_ext (fun x : _86827 => @lem3322986 _86827 s t x)). Qed.
Lemma lem3322990 {_86827 : Type'} : (@all _86827) = (@all _86827).
Proof. exact (eq_refl (@all _86827)). Qed.
Lemma lem3322991 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term2 _86827 s t) = (term35 _86827 s t).
Proof. exact (MK_COMB (@lem3322990 _86827) (@lem3322989 _86827 s t)). Qed.
Lemma lem3322996 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term35 _86827 s t) = (term2 _86827 s t).
Proof. exact (SYM (@lem3322991 _86827 s t)). Qed.
Lemma lem3322998 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3322999 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term35 _86827 s t) = (term37 _86827 s t).
Proof. exact (@lem3322998 (term35 _86827 s t)). Qed.
Lemma lem3323000 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term37 _86827 s t) = (term35 _86827 s t).
Proof. exact (SYM (@lem3322999 _86827 s t)). Qed.
Lemma lem3323001 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term38 _86827 s t) : term38 _86827 s t.
Proof. exact (h1). Qed.
Lemma lem3323004 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term37 _86827 s t) : term37 _86827 s t.
Proof. exact (h1). Qed.
Lemma lem3323005 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term39 _86827 s t.
Proof. exact (fun h0 : term37 _86827 s t => @lem3323004 _86827 s t h0). Qed.
Lemma lem3323006 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term39 _86827 s t) : term39 _86827 s t.
Proof. exact (h1). Qed.
Lemma lem3323007 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term37 _86827 s t) : term37 _86827 s t.
Proof. exact (h1). Qed.
Lemma lem3323008 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term37 _86827 s t) (h2 : term39 _86827 s t) : term37 _86827 s t.
Proof. exact (@lem3323006 _86827 s t h2 (@lem3323007 _86827 s t h1)). Qed.
Lemma lem3323009 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term37 _86827 s t) : term40 _86827 s t.
Proof. exact (fun h0 : term39 _86827 s t => @lem3323008 _86827 s t h1 h0). Qed.
Lemma lem3323010 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term39 _86827 s t) : term39 _86827 s t.
Proof. exact (h1). Qed.
Lemma lem3323011 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term37 _86827 s t) (h2 : term39 _86827 s t) : term37 _86827 s t.
Proof. exact (@lem3323009 _86827 s t h1 (@lem3323010 _86827 s t h2)). Qed.
Lemma lem3323012 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term39 _86827 s t) : term39 _86827 s t.
Proof. exact (fun h0 : term37 _86827 s t => @lem3323011 _86827 s t h0 h1). Qed.
Lemma lem3323013 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term41 _86827 s t.
Proof. exact (fun h0 : term39 _86827 s t => @lem3323012 _86827 s t h0). Qed.
Lemma lem3323016 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term39 _86827 s t.
Proof. exact (@lem3323013 _86827 s t (@lem3323005 _86827 s t)). Qed.
Lemma lem3323017 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term39 _86827 s t.
Proof. exact (@lem3323016 _86827 s t). Qed.
Lemma lem3323027 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3323028 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term37 _86827 s t) = (term42 _86827 s t).
Proof. exact (@lem3323027 (term38 _86827 s t)). Qed.
Lemma lem3323030 (t : Prop) : (term43 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3323031 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term42 _86827 s t) = (term35 _86827 s t).
Proof. exact (@lem3323030 (term35 _86827 s t)). Qed.
Lemma lem3323036 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term37 _86827 s t) = (term35 _86827 s t).
Proof. exact (TRANS (@lem3323028 _86827 s t) (@lem3323031 _86827 s t)). Qed.
Lemma lem3323091 {_86827 : Type'} (t : _86827 -> Prop) : (term44 _86827 t) = (term45 _86827 t).
Proof. exact (fun_ext (fun s : _86827 -> Prop => @lem3323036 _86827 s t)). Qed.
Lemma lem3323092 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323093 {_86827 : Type'} (t : _86827 -> Prop) : (term46 _86827 t) = (term47 _86827 t).
Proof. exact (MK_COMB (@lem3323092 _86827) (@lem3323091 _86827 t)). Qed.
Lemma lem3323098 {_86827 : Type'} : (term48 _86827) = (term49 _86827).
Proof. exact (fun_ext (fun t : _86827 -> Prop => @lem3323093 _86827 t)). Qed.
Lemma lem3323099 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323108 {_86827 : Type'} : (term50 _86827) = (term51 _86827).
Proof. exact (MK_COMB (@lem3323099 _86827) (@lem3323098 _86827)). Qed.
Lemma lem3323113 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term32 _86827 s t x) = (term32 _86827 s t x).
Proof. exact (eq_refl (term32 _86827 s t x)). Qed.
Lemma lem3323122 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term22 _86827 s t t' x) = (term22 _86827 s t t' x).
Proof. exact (eq_refl (term22 _86827 s t t' x)). Qed.
Lemma lem3323123 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term24 _86827 s t x) = (term24 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323122 _86827 s t t' x)). Qed.
Lemma lem3323124 {_86827 : Type'} : (@ex (_86827 -> Prop)) = (@ex (_86827 -> Prop)).
Proof. exact (eq_refl (@ex (_86827 -> Prop))). Qed.
Lemma lem3323125 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term25 _86827 s t x) = (term25 _86827 s t x).
Proof. exact (MK_COMB (@lem3323124 _86827) (@lem3323123 _86827 s t x)). Qed.
Lemma lem3323126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3323127 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term27 _86827 s t x) = (term27 _86827 s t x).
Proof. exact (MK_COMB (@lem3323126) (@lem3323125 _86827 s t x)). Qed.
Lemma lem3323128 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term25 _86827 s t x) = (term32 _86827 s t x)) = ((term25 _86827 s t x) = (term32 _86827 s t x)).
Proof. exact (MK_COMB (@lem3323127 _86827 s t x) (@lem3323113 _86827 s t x)). Qed.
Lemma lem3323129 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term34 _86827 s t) = (term34 _86827 s t).
Proof. exact (fun_ext (fun x : _86827 => @lem3323128 _86827 s t x)). Qed.
Lemma lem3323130 {_86827 : Type'} : (@all _86827) = (@all _86827).
Proof. exact (eq_refl (@all _86827)). Qed.
Lemma lem3323131 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term35 _86827 s t) = (term35 _86827 s t).
Proof. exact (MK_COMB (@lem3323130 _86827) (@lem3323129 _86827 s t)). Qed.
Lemma lem3323132 {_86827 : Type'} (t : _86827 -> Prop) : (term45 _86827 t) = (term45 _86827 t).
Proof. exact (fun_ext (fun s : _86827 -> Prop => @lem3323131 _86827 s t)). Qed.
Lemma lem3323133 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323134 {_86827 : Type'} (t : _86827 -> Prop) : (term47 _86827 t) = (term47 _86827 t).
Proof. exact (MK_COMB (@lem3323133 _86827) (@lem3323132 _86827 t)). Qed.
Lemma lem3323135 {_86827 : Type'} : (term49 _86827) = (term49 _86827).
Proof. exact (fun_ext (fun t : _86827 -> Prop => @lem3323134 _86827 t)). Qed.
Lemma lem3323136 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323137 {_86827 : Type'} : (term51 _86827) = (term51 _86827).
Proof. exact (MK_COMB (@lem3323136 _86827) (@lem3323135 _86827)). Qed.
Lemma lem3323170 {_86827 : Type'} : (term50 _86827) = (term51 _86827).
Proof. exact (TRANS (@lem3323108 _86827) (@lem3323137 _86827)). Qed.
Lemma lem3323171 {_86827 : Type'} : (term51 _86827) = (term50 _86827).
Proof. exact (SYM (@lem3323170 _86827)). Qed.
Lemma lem3323173 (p : Prop) : p = (term36 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3323174 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term25 _86827 s t x) = (term32 _86827 s t x)) = (term52 _86827 s t x).
Proof. exact (@lem3323173 ((term25 _86827 s t x) = (term32 _86827 s t x))). Qed.
Lemma lem3323175 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term52 _86827 s t x) = ((term25 _86827 s t x) = (term32 _86827 s t x)).
Proof. exact (SYM (@lem3323174 _86827 s t x)). Qed.
Lemma lem3323176 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term53 _86827 s t x) : term53 _86827 s t x.
Proof. exact (h1). Qed.
Lemma lem3323185 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term54 _86827 s t' t) = (term55 _86827 s t' t).
Proof. exact (@lem17160 (t' = s) (t' = t)). Qed.
Lemma lem3323189 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (term56 _86827 t' x) = (term56 _86827 t' x).
Proof. exact (eq_refl (term56 _86827 t' x)). Qed.
Lemma lem3323191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3323192 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term57 _86827 s t' t) = (term58 _86827 s t' t).
Proof. exact (MK_COMB (@lem3323191) (@lem3323185 _86827 s t' t)). Qed.
Lemma lem3323193 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term59 _86827 s t t' x) = (term60 _86827 s t t' x).
Proof. exact (MK_COMB (@lem3323192 _86827 s t' t) (@lem3323189 _86827 t' x)). Qed.
Lemma lem3323194 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term61 _86827 s t t' x) = (term59 _86827 s t t' x).
Proof. exact (@lem17045 (term18 _86827 s t' t) (t' x)). Qed.
Lemma lem3323195 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term61 _86827 s t t' x) = (term60 _86827 s t t' x).
Proof. exact (TRANS (@lem3323194 _86827 s t t' x) (@lem3323193 _86827 s t t' x)). Qed.
Lemma lem3323198 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term22 _86827 s t t' x) = (term22 _86827 s t t' x).
Proof. exact (eq_refl (term22 _86827 s t t' x)). Qed.
Lemma lem3323199 {_86827 : Type'} (P : type686 _86827) : (term62 _86827 P) = (term63 _86827 P).
Proof. exact (@lem18394 (_86827 -> Prop) P). Qed.
Lemma lem3323200 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term64 _86827 s t x) = (term65 _86827 s t x).
Proof. exact (@lem3323199 _86827 (term24 _86827 s t x)). Qed.
Lemma lem3323201 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term66 _86827 s t x t') = (term22 _86827 s t t' x).
Proof. exact (eq_refl (term66 _86827 s t x t')). Qed.
Lemma lem3323202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3323203 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term67 _86827 s t x t') = (term61 _86827 s t t' x).
Proof. exact (MK_COMB (@lem3323202) (@lem3323201 _86827 s t t' x)). Qed.
Lemma lem3323204 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term67 _86827 s t x t') = (term60 _86827 s t t' x).
Proof. exact (TRANS (@lem3323203 _86827 s t t' x) (@lem3323195 _86827 s t t' x)). Qed.
Lemma lem3323205 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term68 _86827 s t x) = (term69 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323204 _86827 s t t' x)). Qed.
Lemma lem3323206 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323207 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term65 _86827 s t x) = (term70 _86827 s t x).
Proof. exact (MK_COMB (@lem3323206 _86827) (@lem3323205 _86827 s t x)). Qed.
Lemma lem3323208 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term64 _86827 s t x) = (term70 _86827 s t x).
Proof. exact (TRANS (@lem3323200 _86827 s t x) (@lem3323207 _86827 s t x)). Qed.
Lemma lem3323209 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term24 _86827 s t x) = (term24 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323198 _86827 s t t' x)). Qed.
Lemma lem3323210 {_86827 : Type'} : (@ex (_86827 -> Prop)) = (@ex (_86827 -> Prop)).
Proof. exact (eq_refl (@ex (_86827 -> Prop))). Qed.
Lemma lem3323211 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term25 _86827 s t x) = (term25 _86827 s t x).
Proof. exact (MK_COMB (@lem3323210 _86827) (@lem3323209 _86827 s t x)). Qed.
Lemma lem3323220 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term71 _86827 s t x) = (term72 _86827 s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3323223 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term32 _86827 s t x) = (term32 _86827 s t x).
Proof. exact (eq_refl (term32 _86827 s t x)). Qed.
Lemma lem3323224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3323225 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term73 _86827 s t x) = (term74 _86827 s t x).
Proof. exact (MK_COMB (@lem3323224) (@lem3323208 _86827 s t x)). Qed.
Lemma lem3323226 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term75 _86827 s t x) = (term76 _86827 s t x).
Proof. exact (MK_COMB (@lem3323225 _86827 s t x) (@lem3323223 _86827 s t x)). Qed.
Lemma lem3323227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3323228 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term77 _86827 s t x) = (term77 _86827 s t x).
Proof. exact (MK_COMB (@lem3323227) (@lem3323211 _86827 s t x)). Qed.
Lemma lem3323229 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term78 _86827 s t x) = (term79 _86827 s t x).
Proof. exact (MK_COMB (@lem3323228 _86827 s t x) (@lem3323220 _86827 s t x)). Qed.
Lemma lem3323230 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3323231 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term80 _86827 s t x) = (term81 _86827 s t x).
Proof. exact (MK_COMB (@lem3323230) (@lem3323229 _86827 s t x)). Qed.
Lemma lem3323232 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term82 _86827 s t x) = (term83 _86827 s t x).
Proof. exact (MK_COMB (@lem3323231 _86827 s t x) (@lem3323226 _86827 s t x)). Qed.
Lemma lem3323233 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term53 _86827 s t x) = (term82 _86827 s t x).
Proof. exact (@lem17646 (term25 _86827 s t x) (term32 _86827 s t x)). Qed.
Lemma lem3323234 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term53 _86827 s t x) = (term83 _86827 s t x).
Proof. exact (TRANS (@lem3323233 _86827 s t x) (@lem3323232 _86827 s t x)). Qed.
Lemma lem3323333 {A : Type'} (P : A -> Prop) (Q : Prop) : (term84 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3323334 {_86827 : Type'} (P : type686 _86827) (Q : Prop) : (term86 _86827 P Q) = (term87 _86827 P Q).
Proof. exact (@lem3323333 (_86827 -> Prop) P Q). Qed.
Lemma lem3323335 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term88 _86827 s t x) = (term89 _86827 s t x).
Proof. exact (@lem3323334 _86827 (term24 _86827 s t x) (term72 _86827 s t x)). Qed.
Lemma lem3323336 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term66 _86827 s t x t') = (term22 _86827 s t t' x).
Proof. exact (eq_refl (term66 _86827 s t x t')). Qed.
Lemma lem3323337 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term90 _86827 s t x) = (term24 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323336 _86827 s t t' x)). Qed.
Lemma lem3323338 {_86827 : Type'} : (@ex (_86827 -> Prop)) = (@ex (_86827 -> Prop)).
Proof. exact (eq_refl (@ex (_86827 -> Prop))). Qed.
Lemma lem3323339 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term91 _86827 s t x) = (term25 _86827 s t x).
Proof. exact (MK_COMB (@lem3323338 _86827) (@lem3323337 _86827 s t x)). Qed.
Lemma lem3323340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3323341 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term92 _86827 s t x) = (term77 _86827 s t x).
Proof. exact (MK_COMB (@lem3323340) (@lem3323339 _86827 s t x)). Qed.
Lemma lem3323342 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term72 _86827 s t x) = (term72 _86827 s t x).
Proof. exact (eq_refl (term72 _86827 s t x)). Qed.
Lemma lem3323343 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term88 _86827 s t x) = (term79 _86827 s t x).
Proof. exact (MK_COMB (@lem3323341 _86827 s t x) (@lem3323342 _86827 s t x)). Qed.
Lemma lem3323344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3323345 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term93 _86827 s t x) = (term94 _86827 s t x).
Proof. exact (MK_COMB (@lem3323344) (@lem3323343 _86827 s t x)). Qed.
Lemma lem3323346 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term66 _86827 s t x t') = (term22 _86827 s t t' x).
Proof. exact (eq_refl (term66 _86827 s t x t')). Qed.
Lemma lem3323347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3323348 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term95 _86827 s t x t') = (term96 _86827 s t t' x).
Proof. exact (MK_COMB (@lem3323347) (@lem3323346 _86827 s t t' x)). Qed.
Lemma lem3323349 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term72 _86827 s t x) = (term72 _86827 s t x).
Proof. exact (eq_refl (term72 _86827 s t x)). Qed.
Lemma lem3323350 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term97 _86827 t' s t x) = (term98 _86827 t' s t x).
Proof. exact (MK_COMB (@lem3323348 _86827 s t t' x) (@lem3323349 _86827 s t x)). Qed.
Lemma lem3323351 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term99 _86827 s t x) = (term100 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323350 _86827 t' s t x)). Qed.
Lemma lem3323352 {_86827 : Type'} : (@ex (_86827 -> Prop)) = (@ex (_86827 -> Prop)).
Proof. exact (eq_refl (@ex (_86827 -> Prop))). Qed.
Lemma lem3323353 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term89 _86827 s t x) = (term101 _86827 s t x).
Proof. exact (MK_COMB (@lem3323352 _86827) (@lem3323351 _86827 s t x)). Qed.
Lemma lem3323354 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term88 _86827 s t x) = (term89 _86827 s t x)) = ((term79 _86827 s t x) = (term101 _86827 s t x)).
Proof. exact (MK_COMB (@lem3323345 _86827 s t x) (@lem3323353 _86827 s t x)). Qed.
Lemma lem3323355 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term79 _86827 s t x) = (term101 _86827 s t x).
Proof. exact (EQ_MP (@lem3323354 _86827 s t x) (@lem3323335 _86827 s t x)). Qed.
Lemma lem3323356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3323357 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term81 _86827 s t x) = (term102 _86827 s t x).
Proof. exact (MK_COMB (@lem3323356) (@lem3323355 _86827 s t x)). Qed.
Lemma lem3323358 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term76 _86827 s t x) = (term76 _86827 s t x).
Proof. exact (eq_refl (term76 _86827 s t x)). Qed.
Lemma lem3323359 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term83 _86827 s t x) = (term103 _86827 s t x).
Proof. exact (MK_COMB (@lem3323357 _86827 s t x) (@lem3323358 _86827 s t x)). Qed.
Lemma lem3323361 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3323362 {_86827 : Type'} (P : type686 _86827) (Q : Prop) : (term106 _86827 P Q) = (term107 _86827 P Q).
Proof. exact (@lem3323361 (_86827 -> Prop) P Q). Qed.
Lemma lem3323363 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term108 _86827 s t x) = (term109 _86827 s t x).
Proof. exact (@lem3323362 _86827 (term100 _86827 s t x) (term76 _86827 s t x)). Qed.
Lemma lem3323364 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term110 _86827 s t x t') = (term98 _86827 t' s t x).
Proof. exact (eq_refl (term110 _86827 s t x t')). Qed.
Lemma lem3323365 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term111 _86827 s t x) = (term100 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323364 _86827 t' s t x)). Qed.
Lemma lem3323366 {_86827 : Type'} : (@ex (_86827 -> Prop)) = (@ex (_86827 -> Prop)).
Proof. exact (eq_refl (@ex (_86827 -> Prop))). Qed.
Lemma lem3323367 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term112 _86827 s t x) = (term101 _86827 s t x).
Proof. exact (MK_COMB (@lem3323366 _86827) (@lem3323365 _86827 s t x)). Qed.
Lemma lem3323368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3323369 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term113 _86827 s t x) = (term102 _86827 s t x).
Proof. exact (MK_COMB (@lem3323368) (@lem3323367 _86827 s t x)). Qed.
Lemma lem3323370 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term76 _86827 s t x) = (term76 _86827 s t x).
Proof. exact (eq_refl (term76 _86827 s t x)). Qed.
Lemma lem3323371 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term108 _86827 s t x) = (term103 _86827 s t x).
Proof. exact (MK_COMB (@lem3323369 _86827 s t x) (@lem3323370 _86827 s t x)). Qed.
Lemma lem3323372 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3323373 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term114 _86827 s t x) = (term115 _86827 s t x).
Proof. exact (MK_COMB (@lem3323372) (@lem3323371 _86827 s t x)). Qed.
Lemma lem3323374 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term110 _86827 s t x t') = (term98 _86827 t' s t x).
Proof. exact (eq_refl (term110 _86827 s t x t')). Qed.
Lemma lem3323375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3323376 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term116 _86827 s t x t') = (term117 _86827 t' s t x).
Proof. exact (MK_COMB (@lem3323375) (@lem3323374 _86827 t' s t x)). Qed.
Lemma lem3323377 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term76 _86827 s t x) = (term76 _86827 s t x).
Proof. exact (eq_refl (term76 _86827 s t x)). Qed.
Lemma lem3323378 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term118 _86827 t' s t x) = (term119 _86827 t' s t x).
Proof. exact (MK_COMB (@lem3323376 _86827 t' s t x) (@lem3323377 _86827 s t x)). Qed.
Lemma lem3323379 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term120 _86827 s t x) = (term121 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323378 _86827 t' s t x)). Qed.
Lemma lem3323380 {_86827 : Type'} : (@ex (_86827 -> Prop)) = (@ex (_86827 -> Prop)).
Proof. exact (eq_refl (@ex (_86827 -> Prop))). Qed.
Lemma lem3323381 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term109 _86827 s t x) = (term122 _86827 s t x).
Proof. exact (MK_COMB (@lem3323380 _86827) (@lem3323379 _86827 s t x)). Qed.
Lemma lem3323382 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term108 _86827 s t x) = (term109 _86827 s t x)) = ((term103 _86827 s t x) = (term122 _86827 s t x)).
Proof. exact (MK_COMB (@lem3323373 _86827 s t x) (@lem3323381 _86827 s t x)). Qed.
Lemma lem3323383 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term103 _86827 s t x) = (term122 _86827 s t x).
Proof. exact (EQ_MP (@lem3323382 _86827 s t x) (@lem3323363 _86827 s t x)). Qed.
Lemma lem3323385 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term83 _86827 s t x) = (term122 _86827 s t x).
Proof. exact (TRANS (@lem3323359 _86827 s t x) (@lem3323383 _86827 s t x)). Qed.
Lemma lem3323386 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term53 _86827 s t x) = (term122 _86827 s t x).
Proof. exact (TRANS (@lem3323234 _86827 s t x) (@lem3323385 _86827 s t x)). Qed.
Lemma lem3323387 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term53 _86827 s t x) : term122 _86827 s t x.
Proof. exact (EQ_MP (@lem3323386 _86827 s t x) (@lem3323176 _86827 s t x h1)). Qed.
Lemma lem3323388 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term119 _86827 t' s t x) : term119 _86827 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3323393 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3323394 {_86827 : Type'} (f : _86827 -> Prop) (x : _86827) : (f x) = (@I (_86827 -> Prop) f x).
Proof. exact (@lem3323393 _86827 Prop f x). Qed.
Lemma lem3323396 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (t x) = (@I (_86827 -> Prop) t x).
Proof. exact (@lem3323394 _86827 t x). Qed.
Lemma lem3323401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3323402 {_86827 : Type'} (f : _86827 -> Prop) (x : _86827) : (f x) = (@I (_86827 -> Prop) f x).
Proof. exact (@lem3323401 _86827 Prop f x). Qed.
Lemma lem3323404 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (s x) = (@I (_86827 -> Prop) s x).
Proof. exact (@lem3323402 _86827 s x). Qed.
Lemma lem3323405 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3323406 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term31 _86827 s x) = (term123 _86827 s x).
Proof. exact (MK_COMB (@lem3323405) (@lem3323404 _86827 s x)). Qed.
Lemma lem3323407 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term32 _86827 s t x) = (term124 _86827 s t x).
Proof. exact (MK_COMB (@lem3323406 _86827 s x) (@lem3323396 _86827 t x)). Qed.
Lemma lem3323408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3323413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3323414 {_86827 : Type'} (f : _86827 -> Prop) (x : _86827) : (f x) = (@I (_86827 -> Prop) f x).
Proof. exact (@lem3323413 _86827 Prop f x). Qed.
Lemma lem3323416 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (t' x) = (@I (_86827 -> Prop) t' x).
Proof. exact (@lem3323414 _86827 t' x). Qed.
Lemma lem3323417 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (term56 _86827 t' x) = (term125 _86827 t' x).
Proof. exact (MK_COMB (@lem3323408) (@lem3323416 _86827 t' x)). Qed.
Lemma lem3323436 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term58 _86827 s t' t) = (term58 _86827 s t' t).
Proof. exact (eq_refl (term58 _86827 s t' t)). Qed.
Lemma lem3323437 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term60 _86827 s t t' x) = (term126 _86827 s t t' x).
Proof. exact (MK_COMB (@lem3323436 _86827 s t' t) (@lem3323417 _86827 t' x)). Qed.
Lemma lem3323438 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term69 _86827 s t x) = (term127 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323437 _86827 s t t' x)). Qed.
Lemma lem3323439 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323440 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term70 _86827 s t x) = (term128 _86827 s t x).
Proof. exact (MK_COMB (@lem3323439 _86827) (@lem3323438 _86827 s t x)). Qed.
Lemma lem3323441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3323442 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term74 _86827 s t x) = (term129 _86827 s t x).
Proof. exact (MK_COMB (@lem3323441) (@lem3323440 _86827 s t x)). Qed.
Lemma lem3323443 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term76 _86827 s t x) = (term130 _86827 s t x).
Proof. exact (MK_COMB (@lem3323442 _86827 s t x) (@lem3323407 _86827 s t x)). Qed.
Lemma lem3323444 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3323449 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3323450 {_86827 : Type'} (f : _86827 -> Prop) (x : _86827) : (f x) = (@I (_86827 -> Prop) f x).
Proof. exact (@lem3323449 _86827 Prop f x). Qed.
Lemma lem3323452 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (t x) = (@I (_86827 -> Prop) t x).
Proof. exact (@lem3323450 _86827 t x). Qed.
Lemma lem3323453 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (term56 _86827 t x) = (term125 _86827 t x).
Proof. exact (MK_COMB (@lem3323444) (@lem3323452 _86827 t x)). Qed.
Lemma lem3323454 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3323459 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3323460 {_86827 : Type'} (f : _86827 -> Prop) (x : _86827) : (f x) = (@I (_86827 -> Prop) f x).
Proof. exact (@lem3323459 _86827 Prop f x). Qed.
Lemma lem3323462 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (s x) = (@I (_86827 -> Prop) s x).
Proof. exact (@lem3323460 _86827 s x). Qed.
Lemma lem3323463 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term56 _86827 s x) = (term125 _86827 s x).
Proof. exact (MK_COMB (@lem3323454) (@lem3323462 _86827 s x)). Qed.
Lemma lem3323464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3323465 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term131 _86827 s x) = (term132 _86827 s x).
Proof. exact (MK_COMB (@lem3323464) (@lem3323463 _86827 s x)). Qed.
Lemma lem3323466 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term72 _86827 s t x) = (term133 _86827 s t x).
Proof. exact (MK_COMB (@lem3323465 _86827 s x) (@lem3323453 _86827 t x)). Qed.
Lemma lem3323471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3323472 {_86827 : Type'} (f : _86827 -> Prop) (x : _86827) : (f x) = (@I (_86827 -> Prop) f x).
Proof. exact (@lem3323471 _86827 Prop f x). Qed.
Lemma lem3323474 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (t' x) = (@I (_86827 -> Prop) t' x).
Proof. exact (@lem3323472 _86827 t' x). Qed.
Lemma lem3323489 {_86827 : Type'} (s : _86827 -> Prop) (t' : _86827 -> Prop) (t : _86827 -> Prop) : (term20 _86827 s t' t) = (term20 _86827 s t' t).
Proof. exact (eq_refl (term20 _86827 s t' t)). Qed.
Lemma lem3323490 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term22 _86827 s t t' x) = (term134 _86827 s t t' x).
Proof. exact (MK_COMB (@lem3323489 _86827 s t' t) (@lem3323474 _86827 t' x)). Qed.
Lemma lem3323491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3323492 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term96 _86827 s t t' x) = (term135 _86827 s t t' x).
Proof. exact (MK_COMB (@lem3323491) (@lem3323490 _86827 s t t' x)). Qed.
Lemma lem3323493 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term98 _86827 t' s t x) = (term136 _86827 t' s t x).
Proof. exact (MK_COMB (@lem3323492 _86827 s t t' x) (@lem3323466 _86827 s t x)). Qed.
Lemma lem3323494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3323495 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term117 _86827 t' s t x) = (term137 _86827 t' s t x).
Proof. exact (MK_COMB (@lem3323494) (@lem3323493 _86827 t' s t x)). Qed.
Lemma lem3323496 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term119 _86827 t' s t x) = (term138 _86827 t' s t x).
Proof. exact (MK_COMB (@lem3323495 _86827 t' s t x) (@lem3323443 _86827 s t x)). Qed.
Lemma lem3323497 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term119 _86827 t' s t x) : term138 _86827 t' s t x.
Proof. exact (EQ_MP (@lem3323496 _86827 t' s t x) (@lem3323388 _86827 t' s t x h1)). Qed.
Lemma lem3323498 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term136 _86827 t' s t x.
Proof. exact (h1). Qed.
Lemma lem3323499 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term130 _86827 s t x.
Proof. exact (h1). Qed.
Lemma lem3323500 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term133 _86827 s t x.
Proof. exact (proj2 (@lem3323498 _86827 t' s t x h1)). Qed.
Lemma lem3323501 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term134 _86827 s t t' x.
Proof. exact (proj1 (@lem3323498 _86827 t' s t x h1)). Qed.
Lemma lem3323505 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term18 _86827 s t' t.
Proof. exact (proj1 (@lem3323501 _86827 t' s t x h1)). Qed.
Lemma lem3323508 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term124 _86827 s t x.
Proof. exact (proj2 (@lem3323499 _86827 s t x h1)). Qed.
Lemma lem3323509 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term128 _86827 s t x.
Proof. exact (proj1 (@lem3323499 _86827 s t x h1)). Qed.
Lemma lem3323527 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : t' = s) : t' = s.
Proof. exact (h1). Qed.
Lemma lem3323543 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : t' = t) : t' = t.
Proof. exact (h1). Qed.
Lemma lem3323561 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term126 _86827 s t t' x) = (term139 _86827 s t t' x).
Proof. exact (@lem19699 (term140 _86827 t' s) (term140 _86827 t' t) (term125 _86827 t' x)). Qed.
Lemma lem3323562 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term127 _86827 s t x) = (term141 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323561 _86827 s t t' x)). Qed.
Lemma lem3323563 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323565 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term128 _86827 s t x) = (term142 _86827 s t x).
Proof. exact (MK_COMB (@lem3323563 _86827) (@lem3323562 _86827 s t x)). Qed.
Lemma lem3323566 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term142 _86827 s t x.
Proof. exact (EQ_MP (@lem3323565 _86827 s t x) (@lem3323509 _86827 s t x h1)). Qed.
Lemma lem3323570 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) s x) : @I (_86827 -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3323588 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (t' : _86827 -> Prop) (x : _86827) : (term126 _86827 s t t' x) = (term139 _86827 s t t' x).
Proof. exact (@lem19699 (term140 _86827 t' s) (term140 _86827 t' t) (term125 _86827 t' x)). Qed.
Lemma lem3323589 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term127 _86827 s t x) = (term141 _86827 s t x).
Proof. exact (fun_ext (fun t' : _86827 -> Prop => @lem3323588 _86827 s t t' x)). Qed.
Lemma lem3323590 {_86827 : Type'} : (@all (_86827 -> Prop)) = (@all (_86827 -> Prop)).
Proof. exact (eq_refl (@all (_86827 -> Prop))). Qed.
Lemma lem3323592 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term128 _86827 s t x) = (term142 _86827 s t x).
Proof. exact (MK_COMB (@lem3323590 _86827) (@lem3323589 _86827 s t x)). Qed.
Lemma lem3323593 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term142 _86827 s t x.
Proof. exact (EQ_MP (@lem3323592 _86827 s t x) (@lem3323509 _86827 s t x h1)). Qed.
Lemma lem3323597 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) t x) : @I (_86827 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3323598 {_86827 : Type'} (_34475 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term143 _86827 s t x _34475.
Proof. exact (@lem3323566 _86827 s t x h1 _34475). Qed.
Lemma lem3323599 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (_34475 : _86827 -> Prop) (x : _86827) : (term143 _86827 s t x _34475) = (term139 _86827 s t _34475 x).
Proof. exact (eq_refl (term143 _86827 s t x _34475)). Qed.
Lemma lem3323600 {_86827 : Type'} (_34475 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term139 _86827 s t _34475 x.
Proof. exact (EQ_MP (@lem3323599 _86827 s t _34475 x) (@lem3323598 _86827 _34475 s t x h1)). Qed.
Lemma lem3323601 {_86827 : Type'} (_34476 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term143 _86827 s t x _34476.
Proof. exact (@lem3323593 _86827 s t x h1 _34476). Qed.
Lemma lem3323602 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (_34476 : _86827 -> Prop) (x : _86827) : (term143 _86827 s t x _34476) = (term139 _86827 s t _34476 x).
Proof. exact (eq_refl (term143 _86827 s t x _34476)). Qed.
Lemma lem3323603 {_86827 : Type'} (_34476 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term139 _86827 s t _34476 x.
Proof. exact (EQ_MP (@lem3323602 _86827 s t _34476 x) (@lem3323601 _86827 _34476 s t x h1)). Qed.
Lemma lem3323613 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : @I (_86827 -> Prop) t' x.
Proof. exact (proj2 (@lem3323501 _86827 t' s t x h1)). Qed.
Lemma lem3323615 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : t' = s) : t' = s.
Proof. exact (h1). Qed.
Lemma lem3323621 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : @I (_86827 -> Prop) t' x.
Proof. exact (proj2 (@lem3323501 _86827 t' s t x h1)). Qed.
Lemma lem3323623 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : t' = t) : t' = t.
Proof. exact (h1). Qed.
Lemma lem3323625 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) s x) : @I (_86827 -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3323631 {_86827 : Type'} (_34475 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term144 _86827 s _34475 x.
Proof. exact (proj1 (@lem3323600 _86827 _34475 s t x h1)). Qed.
Lemma lem3323639 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) t x) : @I (_86827 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3323651 {_86827 : Type'} (_34476 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term144 _86827 t _34476 x.
Proof. exact (proj2 (@lem3323603 _86827 _34476 s t x h1)). Qed.
Lemma lem3323679 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term125 _86827 s x.
Proof. exact (proj1 (@lem3323500 _86827 t' s t x h1)). Qed.
Lemma lem3323694 {_86827 : Type'} (x : _86827) : (term145 _86827 x) = (term145 _86827 x).
Proof. exact (eq_refl (term145 _86827 x)). Qed.
Lemma lem3323695 {_86827 : Type'} (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : t' = s) : (term146 _86827 x t') = (term146 _86827 x s).
Proof. exact (MK_COMB (@lem3323694 _86827 x) (@lem3323615 _86827 t' s h1)). Qed.
Lemma lem3323696 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term146 _86827 x s) = (@I (_86827 -> Prop) s x).
Proof. exact (eq_refl (term146 _86827 x s)). Qed.
Lemma lem3323697 {_86827 : Type'} (x : _86827) (t' : _86827 -> Prop) : (term147 _86827 x t') = (term147 _86827 x t').
Proof. exact (eq_refl (term147 _86827 x t')). Qed.
Lemma lem3323698 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) : ((term146 _86827 x t') = (term146 _86827 x s)) = ((term146 _86827 x t') = (@I (_86827 -> Prop) s x)).
Proof. exact (MK_COMB (@lem3323697 _86827 x t') (@lem3323696 _86827 s x)). Qed.
Lemma lem3323699 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (term146 _86827 x t') = (@I (_86827 -> Prop) t' x).
Proof. exact (eq_refl (term146 _86827 x t')). Qed.
Lemma lem3323700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3323701 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (term147 _86827 x t') = (term148 _86827 t' x).
Proof. exact (MK_COMB (@lem3323700) (@lem3323699 _86827 t' x)). Qed.
Lemma lem3323702 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (@I (_86827 -> Prop) s x) = (@I (_86827 -> Prop) s x).
Proof. exact (eq_refl (@I (_86827 -> Prop) s x)). Qed.
Lemma lem3323703 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) : ((term146 _86827 x t') = (@I (_86827 -> Prop) s x)) = ((@I (_86827 -> Prop) t' x) = (@I (_86827 -> Prop) s x)).
Proof. exact (MK_COMB (@lem3323701 _86827 t' x) (@lem3323702 _86827 s x)). Qed.
Lemma lem3323704 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) : ((term146 _86827 x t') = (term146 _86827 x s)) = ((@I (_86827 -> Prop) t' x) = (@I (_86827 -> Prop) s x)).
Proof. exact (TRANS (@lem3323698 _86827 t' s x) (@lem3323703 _86827 t' s x)). Qed.
Lemma lem3323705 {_86827 : Type'} (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : t' = s) : (@I (_86827 -> Prop) t' x) = (@I (_86827 -> Prop) s x).
Proof. exact (EQ_MP (@lem3323704 _86827 t' s x) (@lem3323695 _86827 x t' s h1)). Qed.
Lemma lem3323748 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term125 _86827 t x.
Proof. exact (proj2 (@lem3323500 _86827 t' s t x h1)). Qed.
Lemma lem3323749 {_86827 : Type'} (x : _86827) : (term145 _86827 x) = (term145 _86827 x).
Proof. exact (eq_refl (term145 _86827 x)). Qed.
Lemma lem3323750 {_86827 : Type'} (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : t' = t) : (term146 _86827 x t') = (term146 _86827 x t).
Proof. exact (MK_COMB (@lem3323749 _86827 x) (@lem3323623 _86827 t' t h1)). Qed.
Lemma lem3323751 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (term146 _86827 x t) = (@I (_86827 -> Prop) t x).
Proof. exact (eq_refl (term146 _86827 x t)). Qed.
Lemma lem3323752 {_86827 : Type'} (x : _86827) (t' : _86827 -> Prop) : (term147 _86827 x t') = (term147 _86827 x t').
Proof. exact (eq_refl (term147 _86827 x t')). Qed.
Lemma lem3323753 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term146 _86827 x t') = (term146 _86827 x t)) = ((term146 _86827 x t') = (@I (_86827 -> Prop) t x)).
Proof. exact (MK_COMB (@lem3323752 _86827 x t') (@lem3323751 _86827 t x)). Qed.
Lemma lem3323754 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (term146 _86827 x t') = (@I (_86827 -> Prop) t' x).
Proof. exact (eq_refl (term146 _86827 x t')). Qed.
Lemma lem3323755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3323756 {_86827 : Type'} (t' : _86827 -> Prop) (x : _86827) : (term147 _86827 x t') = (term148 _86827 t' x).
Proof. exact (MK_COMB (@lem3323755) (@lem3323754 _86827 t' x)). Qed.
Lemma lem3323757 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (@I (_86827 -> Prop) t x) = (@I (_86827 -> Prop) t x).
Proof. exact (eq_refl (@I (_86827 -> Prop) t x)). Qed.
Lemma lem3323758 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term146 _86827 x t') = (@I (_86827 -> Prop) t x)) = ((@I (_86827 -> Prop) t' x) = (@I (_86827 -> Prop) t x)).
Proof. exact (MK_COMB (@lem3323756 _86827 t' x) (@lem3323757 _86827 t x)). Qed.
Lemma lem3323759 {_86827 : Type'} (t' : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : ((term146 _86827 x t') = (term146 _86827 x t)) = ((@I (_86827 -> Prop) t' x) = (@I (_86827 -> Prop) t x)).
Proof. exact (TRANS (@lem3323753 _86827 t' t x) (@lem3323758 _86827 t' t x)). Qed.
Lemma lem3323760 {_86827 : Type'} (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : t' = t) : (@I (_86827 -> Prop) t' x) = (@I (_86827 -> Prop) t x).
Proof. exact (EQ_MP (@lem3323759 _86827 t' t x) (@lem3323750 _86827 x t' t h1)). Qed.
Lemma lem3323763 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : @I (_86827 -> Prop) s x.
Proof. exact (EQ_MP (@lem3323705 _86827 x t' s h2) (@lem3323613 _86827 t' s t x h1)). Qed.
Lemma lem3323764 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : term149 _86827 s x.
Proof. exact (fun h0 : term125 _86827 s x => @lem3323763 _86827 t x t' s h1 h2). Qed.
Lemma lem3323766 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323767 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term149 _86827 s x) = (@I (_86827 -> Prop) s x).
Proof. exact (@lem3323766 (@I (_86827 -> Prop) s x)). Qed.
Lemma lem3323768 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : @I (_86827 -> Prop) s x.
Proof. exact (EQ_MP (@lem3323767 _86827 s x) (@lem3323764 _86827 t x t' s h1 h2)). Qed.
Lemma lem3323771 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3323773 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term125 _86827 s x) = (term151 _86827 s x).
Proof. exact (@lem3323771 (@I (_86827 -> Prop) s x)). Qed.
Lemma lem3323776 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term151 _86827 s x.
Proof. exact (EQ_MP (@lem3323773 _86827 s x) (@lem3323679 _86827 t' s t x h1)). Qed.
Lemma lem3323779 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : False.
Proof. exact (@lem3323776 _86827 t' s t x h1 (@lem3323768 _86827 t x t' s h1 h2)). Qed.
Lemma lem3323780 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : term152.
Proof. exact (fun h0 : ~ False => @lem3323779 _86827 t x t' s h1 h2). Qed.
Lemma lem3323782 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323783 : term152 = False.
Proof. exact (@lem3323782 False). Qed.
Lemma lem3323786 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : @I (_86827 -> Prop) t x.
Proof. exact (EQ_MP (@lem3323760 _86827 x t' t h2) (@lem3323621 _86827 t' s t x h1)). Qed.
Lemma lem3323787 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : term149 _86827 t x.
Proof. exact (fun h0 : term125 _86827 t x => @lem3323786 _86827 s x t' t h1 h2). Qed.
Lemma lem3323789 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323790 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (term149 _86827 t x) = (@I (_86827 -> Prop) t x).
Proof. exact (@lem3323789 (@I (_86827 -> Prop) t x)). Qed.
Lemma lem3323791 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : @I (_86827 -> Prop) t x.
Proof. exact (EQ_MP (@lem3323790 _86827 t x) (@lem3323787 _86827 s x t' t h1 h2)). Qed.
Lemma lem3323794 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3323796 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (term125 _86827 t x) = (term151 _86827 t x).
Proof. exact (@lem3323794 (@I (_86827 -> Prop) t x)). Qed.
Lemma lem3323799 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : term151 _86827 t x.
Proof. exact (EQ_MP (@lem3323796 _86827 t x) (@lem3323748 _86827 t' s t x h1)). Qed.
Lemma lem3323802 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : False.
Proof. exact (@lem3323799 _86827 t' s t x h1 (@lem3323791 _86827 s x t' t h1 h2)). Qed.
Lemma lem3323803 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : term152.
Proof. exact (fun h0 : ~ False => @lem3323802 _86827 s x t' t h1 h2). Qed.
Lemma lem3323805 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323806 : term152 = False.
Proof. exact (@lem3323805 False). Qed.
Lemma lem3323832 {_86827 : Type'} (x : _86827 -> Prop) : x = x.
Proof. exact (@lem21386 (_86827 -> Prop) x). Qed.
Lemma lem3323833 {_86827 : Type'} (x : _86827 -> Prop) : x = x.
Proof. exact (@lem3323832 _86827 x). Qed.
Lemma lem3323834 {_86827 : Type'} (s : _86827 -> Prop) : s = s.
Proof. exact (@lem3323833 _86827 s). Qed.
Lemma lem3323835 {_86827 : Type'} (s : _86827 -> Prop) : term153 _86827 s.
Proof. exact (fun h0 : term154 _86827 s => @lem3323834 _86827 s). Qed.
Lemma lem3323837 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323838 {_86827 : Type'} (s : _86827 -> Prop) : (term153 _86827 s) = (s = s).
Proof. exact (@lem3323837 (s = s)). Qed.
Lemma lem3323839 {_86827 : Type'} (s : _86827 -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3323838 _86827 s) (@lem3323835 _86827 s)). Qed.
Lemma lem3323841 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) s x) : @I (_86827 -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3323842 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) s x) : term149 _86827 s x.
Proof. exact (fun h0 : term125 _86827 s x => @lem3323841 _86827 s x h1). Qed.
Lemma lem3323844 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323845 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) : (term149 _86827 s x) = (@I (_86827 -> Prop) s x).
Proof. exact (@lem3323844 (@I (_86827 -> Prop) s x)). Qed.
Lemma lem3323846 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) s x) : @I (_86827 -> Prop) s x.
Proof. exact (EQ_MP (@lem3323845 _86827 s x) (@lem3323842 _86827 s x h1)). Qed.
Lemma lem3323848 (a : Prop) (b : Prop) : (term155 a b) = (term156 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3323849 {_86827 : Type'} (s : _86827 -> Prop) (_34475 : _86827 -> Prop) (x : _86827) : (term144 _86827 s _34475 x) = (term157 _86827 s _34475 x).
Proof. exact (@lem3323848 (_34475 = s) (@I (_86827 -> Prop) _34475 x)). Qed.
Lemma lem3323851 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3323852 {_86827 : Type'} (s : _86827 -> Prop) (_34475 : _86827 -> Prop) (x : _86827) : (term157 _86827 s _34475 x) = (term158 _86827 s _34475 x).
Proof. exact (@lem3323851 (term159 _86827 s _34475 x)). Qed.
Lemma lem3323853 {_86827 : Type'} (s : _86827 -> Prop) (_34475 : _86827 -> Prop) (x : _86827) : (term144 _86827 s _34475 x) = (term158 _86827 s _34475 x).
Proof. exact (TRANS (@lem3323849 _86827 s _34475 x) (@lem3323852 _86827 s _34475 x)). Qed.
Lemma lem3323855 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) s x) : term160 _86827 s x.
Proof. exact (conj (@lem3323839 _86827 s) (@lem3323846 _86827 s x h1)). Qed.
Lemma lem3323857 {_86827 : Type'} (_34475 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term158 _86827 s _34475 x.
Proof. exact (EQ_MP (@lem3323853 _86827 s _34475 x) (@lem3323631 _86827 _34475 s t x h1)). Qed.
Lemma lem3323858 {_86827 : Type'} (_34475 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term158 _86827 s _34475 x.
Proof. exact (@lem3323857 _86827 _34475 s t x h1). Qed.
Lemma lem3323859 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term161 _86827 s x.
Proof. exact (@lem3323858 _86827 s s t x h1). Qed.
Lemma lem3323862 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : False.
Proof. exact (@lem3323859 _86827 s t x h1 (@lem3323855 _86827 s x h2)). Qed.
Lemma lem3323863 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : term152.
Proof. exact (fun h0 : ~ False => @lem3323862 _86827 t s x h1 h2). Qed.
Lemma lem3323865 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323866 : term152 = False.
Proof. exact (@lem3323865 False). Qed.
Lemma lem3323867 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3323866) (@lem3323863 _86827 t s x h1 h2)). Qed.
Lemma lem3323892 {_86827 : Type'} (x : _86827 -> Prop) : x = x.
Proof. exact (@lem21386 (_86827 -> Prop) x). Qed.
Lemma lem3323893 {_86827 : Type'} (x : _86827 -> Prop) : x = x.
Proof. exact (@lem3323892 _86827 x). Qed.
Lemma lem3323894 {_86827 : Type'} (t : _86827 -> Prop) : t = t.
Proof. exact (@lem3323893 _86827 t). Qed.
Lemma lem3323895 {_86827 : Type'} (t : _86827 -> Prop) : term153 _86827 t.
Proof. exact (fun h0 : term154 _86827 t => @lem3323894 _86827 t). Qed.
Lemma lem3323897 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323898 {_86827 : Type'} (t : _86827 -> Prop) : (term153 _86827 t) = (t = t).
Proof. exact (@lem3323897 (t = t)). Qed.
Lemma lem3323899 {_86827 : Type'} (t : _86827 -> Prop) : t = t.
Proof. exact (EQ_MP (@lem3323898 _86827 t) (@lem3323895 _86827 t)). Qed.
Lemma lem3323901 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) t x) : @I (_86827 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3323902 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) t x) : term149 _86827 t x.
Proof. exact (fun h0 : term125 _86827 t x => @lem3323901 _86827 t x h1). Qed.
Lemma lem3323904 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323905 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) : (term149 _86827 t x) = (@I (_86827 -> Prop) t x).
Proof. exact (@lem3323904 (@I (_86827 -> Prop) t x)). Qed.
Lemma lem3323906 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) t x) : @I (_86827 -> Prop) t x.
Proof. exact (EQ_MP (@lem3323905 _86827 t x) (@lem3323902 _86827 t x h1)). Qed.
Lemma lem3323908 (a : Prop) (b : Prop) : (term155 a b) = (term156 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3323909 {_86827 : Type'} (t : _86827 -> Prop) (_34476 : _86827 -> Prop) (x : _86827) : (term144 _86827 t _34476 x) = (term157 _86827 t _34476 x).
Proof. exact (@lem3323908 (_34476 = t) (@I (_86827 -> Prop) _34476 x)). Qed.
Lemma lem3323911 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3323912 {_86827 : Type'} (t : _86827 -> Prop) (_34476 : _86827 -> Prop) (x : _86827) : (term157 _86827 t _34476 x) = (term158 _86827 t _34476 x).
Proof. exact (@lem3323911 (term159 _86827 t _34476 x)). Qed.
Lemma lem3323913 {_86827 : Type'} (t : _86827 -> Prop) (_34476 : _86827 -> Prop) (x : _86827) : (term144 _86827 t _34476 x) = (term158 _86827 t _34476 x).
Proof. exact (TRANS (@lem3323909 _86827 t _34476 x) (@lem3323912 _86827 t _34476 x)). Qed.
Lemma lem3323915 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (h1 : @I (_86827 -> Prop) t x) : term160 _86827 t x.
Proof. exact (conj (@lem3323899 _86827 t) (@lem3323906 _86827 t x h1)). Qed.
Lemma lem3323917 {_86827 : Type'} (_34476 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term158 _86827 t _34476 x.
Proof. exact (EQ_MP (@lem3323913 _86827 t _34476 x) (@lem3323651 _86827 _34476 s t x h1)). Qed.
Lemma lem3323918 {_86827 : Type'} (_34476 : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term158 _86827 t _34476 x.
Proof. exact (@lem3323917 _86827 _34476 s t x h1). Qed.
Lemma lem3323919 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : term161 _86827 t x.
Proof. exact (@lem3323918 _86827 t s t x h1). Qed.
Lemma lem3323922 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : False.
Proof. exact (@lem3323919 _86827 s t x h1 (@lem3323915 _86827 t x h2)). Qed.
Lemma lem3323923 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : term152.
Proof. exact (fun h0 : ~ False => @lem3323922 _86827 s t x h1 h2). Qed.
Lemma lem3323925 (p : Prop) : (term150 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3323926 : term152 = False.
Proof. exact (@lem3323925 False). Qed.
Lemma lem3323927 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3323926) (@lem3323923 _86827 s t x h1 h2)). Qed.
Lemma lem3323928 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3323806) (@lem3323803 _86827 s x t' t h1 h2)). Qed.
Lemma lem3323929 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3323783) (@lem3323780 _86827 t x t' s h1 h2)). Qed.
Lemma lem3323930 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : (@I (_86827 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86827 -> Prop) t x => @lem3323927 _86827 s t x h1 h2) (fun h3 : False => @lem3323639 _86827 t x h2)). Qed.
Lemma lem3323931 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3323930 _86827 s t x h1 h2) (@lem3323639 _86827 t x h2)). Qed.
Lemma lem3323932 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : (@I (_86827 -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86827 -> Prop) s x => @lem3323867 _86827 t s x h1 h2) (fun h3 : False => @lem3323625 _86827 s x h2)). Qed.
Lemma lem3323933 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3323932 _86827 t s x h1 h2) (@lem3323625 _86827 s x h2)). Qed.
Lemma lem3323934 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : (t' = t) = False.
Proof. exact (prop_ext (fun h3 : t' = t => @lem3323928 _86827 s x t' t h1 h2) (fun h3 : False => @lem3323623 _86827 t' t h2)). Qed.
Lemma lem3323935 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3323934 _86827 s x t' t h1 h2) (@lem3323623 _86827 t' t h2)). Qed.
Lemma lem3323936 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : (t' = s) = False.
Proof. exact (prop_ext (fun h3 : t' = s => @lem3323929 _86827 t x t' s h1 h2) (fun h3 : False => @lem3323615 _86827 t' s h2)). Qed.
Lemma lem3323937 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3323936 _86827 t x t' s h1 h2) (@lem3323615 _86827 t' s h2)). Qed.
Lemma lem3323938 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : (@I (_86827 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86827 -> Prop) t x => @lem3323931 _86827 s t x h1 h2) (fun h3 : False => @lem3323597 _86827 t x h2)). Qed.
Lemma lem3323939 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3323938 _86827 s t x h1 h2) (@lem3323597 _86827 t x h2)). Qed.
Lemma lem3323940 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : (@I (_86827 -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86827 -> Prop) s x => @lem3323933 _86827 t s x h1 h2) (fun h3 : False => @lem3323570 _86827 s x h2)). Qed.
Lemma lem3323941 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3323940 _86827 t s x h1 h2) (@lem3323570 _86827 s x h2)). Qed.
Lemma lem3323942 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : (t' = t) = False.
Proof. exact (prop_ext (fun h3 : t' = t => @lem3323935 _86827 s x t' t h1 h2) (fun h3 : False => @lem3323543 _86827 t' t h2)). Qed.
Lemma lem3323943 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3323942 _86827 s x t' t h1 h2) (@lem3323543 _86827 t' t h2)). Qed.
Lemma lem3323944 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : (t' = s) = False.
Proof. exact (prop_ext (fun h3 : t' = s => @lem3323937 _86827 t x t' s h1 h2) (fun h3 : False => @lem3323527 _86827 t' s h2)). Qed.
Lemma lem3323945 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3323944 _86827 t x t' s h1 h2) (@lem3323527 _86827 t' s h2)). Qed.
Lemma lem3323946 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : (@I (_86827 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86827 -> Prop) t x => @lem3323939 _86827 s t x h1 h2) (fun h3 : False => @lem3323597 _86827 t x h2)). Qed.
Lemma lem3323947 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3323946 _86827 s t x h1 h2) (@lem3323597 _86827 t x h2)). Qed.
Lemma lem3323948 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : (@I (_86827 -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (_86827 -> Prop) s x => @lem3323941 _86827 t s x h1 h2) (fun h3 : False => @lem3323570 _86827 s x h2)). Qed.
Lemma lem3323949 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) (h2 : @I (_86827 -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3323948 _86827 t s x h1 h2) (@lem3323570 _86827 s x h2)). Qed.
Lemma lem3323950 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : (t' = t) = False.
Proof. exact (prop_ext (fun h3 : t' = t => @lem3323943 _86827 s x t' t h1 h2) (fun h3 : False => @lem3323543 _86827 t' t h2)). Qed.
Lemma lem3323951 {_86827 : Type'} (s : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = t) : False.
Proof. exact (EQ_MP (@lem3323950 _86827 s x t' t h1 h2) (@lem3323543 _86827 t' t h2)). Qed.
Lemma lem3323952 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : (t' = s) = False.
Proof. exact (prop_ext (fun h3 : t' = s => @lem3323945 _86827 t x t' s h1 h2) (fun h3 : False => @lem3323527 _86827 t' s h2)). Qed.
Lemma lem3323953 {_86827 : Type'} (t : _86827 -> Prop) (x : _86827) (t' : _86827 -> Prop) (s : _86827 -> Prop) (h1 : term136 _86827 t' s t x) (h2 : t' = s) : False.
Proof. exact (EQ_MP (@lem3323952 _86827 t x t' s h1 h2) (@lem3323527 _86827 t' s h2)). Qed.
Lemma lem3323954 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term130 _86827 s t x) : False.
Proof. exact (or_elim (@lem3323508 _86827 s t x h1) (fun h0 : @I (_86827 -> Prop) s x => @lem3323949 _86827 t s x h1 h0) (fun h0 : @I (_86827 -> Prop) t x => @lem3323947 _86827 s t x h1 h0)). Qed.
Lemma lem3323955 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term136 _86827 t' s t x) : False.
Proof. exact (or_elim (@lem3323505 _86827 t' s t x h1) (fun h0 : t' = s => @lem3323953 _86827 t x t' s h1 h0) (fun h0 : t' = t => @lem3323951 _86827 s x t' t h1 h0)). Qed.
Lemma lem3323956 {_86827 : Type'} (t' : _86827 -> Prop) (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term119 _86827 t' s t x) : False.
Proof. exact (or_elim (@lem3323497 _86827 t' s t x h1) (fun h0 : term136 _86827 t' s t x => @lem3323955 _86827 t' s t x h0) (fun h0 : term130 _86827 s t x => @lem3323954 _86827 s t x h0)). Qed.
Lemma lem3323957 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term53 _86827 s t x) : False.
Proof. exact (ex_elim (@lem3323387 _86827 s t x h1) (fun t' : _86827 -> Prop => fun h0 : term121 _86827 s t x t' => @lem3323956 _86827 t' s t x h0)). Qed.
Lemma lem3323958 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term53 _86827 s t x) : (term53 _86827 s t x) = False.
Proof. exact (prop_ext (fun h2 : term53 _86827 s t x => @lem3323957 _86827 s t x h1) (fun h2 : False => @lem3323176 _86827 s t x h1)). Qed.
Lemma lem3323959 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) (h1 : term53 _86827 s t x) : False.
Proof. exact (EQ_MP (@lem3323958 _86827 s t x h1) (@lem3323176 _86827 s t x h1)). Qed.
Lemma lem3323960 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : term52 _86827 s t x.
Proof. exact (fun h0 : term53 _86827 s t x => @lem3323959 _86827 s t x h0). Qed.
Lemma lem3323961 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (x : _86827) : (term25 _86827 s t x) = (term32 _86827 s t x).
Proof. exact (EQ_MP (@lem3323175 _86827 s t x) (@lem3323960 _86827 s t x)). Qed.
Lemma lem3323966 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term35 _86827 s t.
Proof. exact (fun x : _86827 => @lem3323961 _86827 s t x). Qed.
Lemma lem3323971 {_86827 : Type'} (t : _86827 -> Prop) : term47 _86827 t.
Proof. exact (fun s : _86827 -> Prop => @lem3323966 _86827 s t). Qed.
Lemma lem3323976 {_86827 : Type'} : term51 _86827.
Proof. exact (fun t : _86827 -> Prop => @lem3323971 _86827 t). Qed.
Lemma lem3323977 {_86827 : Type'} : term50 _86827.
Proof. exact (EQ_MP (@lem3323171 _86827) (@lem3323976 _86827)). Qed.
Lemma lem3323978 {_86827 : Type'} (t : _86827 -> Prop) : term162 _86827 t.
Proof. exact (@lem3323977 _86827 t). Qed.
Lemma lem3323979 {_86827 : Type'} (t : _86827 -> Prop) : (term162 _86827 t) = (term46 _86827 t).
Proof. exact (eq_refl (term162 _86827 t)). Qed.
Lemma lem3323980 {_86827 : Type'} (t : _86827 -> Prop) : term46 _86827 t.
Proof. exact (EQ_MP (@lem3323979 _86827 t) (@lem3323978 _86827 t)). Qed.
Lemma lem3323981 {_86827 : Type'} (t : _86827 -> Prop) (s : _86827 -> Prop) : term163 _86827 t s.
Proof. exact (@lem3323980 _86827 t s). Qed.
Lemma lem3323982 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term163 _86827 t s) = (term37 _86827 s t).
Proof. exact (eq_refl (term163 _86827 t s)). Qed.
Lemma lem3323983 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term37 _86827 s t.
Proof. exact (EQ_MP (@lem3323982 _86827 s t) (@lem3323981 _86827 t s)). Qed.
Lemma lem3323985 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term37 _86827 s t.
Proof. exact (@lem3323017 _86827 s t (@lem3323983 _86827 s t)). Qed.
Lemma lem3323986 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term38 _86827 s t) : False.
Proof. exact (@lem3323985 _86827 s t (@lem3323001 _86827 s t h1)). Qed.
Lemma lem3323987 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term38 _86827 s t) : (term38 _86827 s t) = False.
Proof. exact (prop_ext (fun h2 : term38 _86827 s t => @lem3323986 _86827 s t h1) (fun h2 : False => @lem3323001 _86827 s t h1)). Qed.
Lemma lem3323988 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : term38 _86827 s t) : False.
Proof. exact (EQ_MP (@lem3323987 _86827 s t h1) (@lem3323001 _86827 s t h1)). Qed.
Lemma lem3323989 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term37 _86827 s t.
Proof. exact (fun h0 : term38 _86827 s t => @lem3323988 _86827 s t h0). Qed.
Lemma lem3323990 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term35 _86827 s t.
Proof. exact (EQ_MP (@lem3323000 _86827 s t) (@lem3323989 _86827 s t)). Qed.
Lemma lem3323991 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : term2 _86827 s t.
Proof. exact (EQ_MP (@lem3322996 _86827 s t) (@lem3323990 _86827 s t)). Qed.
Lemma lem3323992 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (term1 _86827 s t) = (@UNION _86827 s t).
Proof. exact (EQ_MP (@lem3322897 _86827 s t) (@lem3323991 _86827 s t)). Qed.
