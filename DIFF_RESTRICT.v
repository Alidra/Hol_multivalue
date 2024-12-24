Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_RESTRICT_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3270851 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3270852 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) : (s = t) = (term0 _85837 s t).
Proof. exact (@lem3270851 _85837 s t). Qed.
Lemma lem3270853 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : ((term1 _85837 s t P) = (term2 _85837 s t P)) = (term3 _85837 s t P).
Proof. exact (@lem3270852 _85837 (term1 _85837 s t P) (term2 _85837 s t P)). Qed.
Lemma lem3270880 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term4 _85837 s P) = (term5 _85837 s P).
Proof. exact (fun_ext (fun t : _85837 -> Prop => @lem3270853 _85837 s t P)). Qed.
Lemma lem3270881 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3270882 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term6 _85837 s P) = (term7 _85837 s P).
Proof. exact (MK_COMB (@lem3270881 _85837) (@lem3270880 _85837 s P)). Qed.
Lemma lem3270887 {_85837 : Type'} (P : _85837 -> Prop) : (term8 _85837 P) = (term9 _85837 P).
Proof. exact (fun_ext (fun s : _85837 -> Prop => @lem3270882 _85837 s P)). Qed.
Lemma lem3270888 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3270889 {_85837 : Type'} (P : _85837 -> Prop) : (term10 _85837 P) = (term11 _85837 P).
Proof. exact (MK_COMB (@lem3270888 _85837) (@lem3270887 _85837 P)). Qed.
Lemma lem3270894 {_85837 : Type'} : (term12 _85837) = (term13 _85837).
Proof. exact (fun_ext (fun P : _85837 -> Prop => @lem3270889 _85837 P)). Qed.
Lemma lem3270895 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3270896 {_85837 : Type'} : (term14 _85837) = (term15 _85837).
Proof. exact (MK_COMB (@lem3270895 _85837) (@lem3270894 _85837)). Qed.
Lemma lem3270901 {_85837 : Type'} : (term15 _85837) = (term14 _85837).
Proof. exact (SYM (@lem3270896 _85837)). Qed.
Lemma lem3270921 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3270922 {_85837 : Type'} (p : _85837 -> Prop) (x : _85837) : (term16 _85837 x p) = (p x).
Proof. exact (@lem3270921 _85837 p x). Qed.
Lemma lem3270923 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term17 _85837 x s t P) = (term18 _85837 s t P x).
Proof. exact (@lem3270922 _85837 (term19 _85837 s t P) x). Qed.
Lemma lem3270924 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term18 _85837 s t P x) = (term20 _85837 s t P x).
Proof. exact (eq_refl (term18 _85837 s t P x)). Qed.
Lemma lem3270925 {_85837 : Type'} (GEN_PVAR_18 : _85837) : (@SETSPEC _85837 GEN_PVAR_18) = (@SETSPEC _85837 GEN_PVAR_18).
Proof. exact (eq_refl (@SETSPEC _85837 GEN_PVAR_18)). Qed.
Lemma lem3270926 {_85837 : Type'} (GEN_PVAR_18 : _85837) (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term21 _85837 GEN_PVAR_18 s t P x) = (term22 _85837 GEN_PVAR_18 s t P x).
Proof. exact (MK_COMB (@lem3270925 _85837 GEN_PVAR_18) (@lem3270924 _85837 s t P x)). Qed.
Lemma lem3270927 {_85837 : Type'} (x : _85837) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3270928 {_85837 : Type'} (GEN_PVAR_18 : _85837) (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term23 _85837 GEN_PVAR_18 s t P x) = (term24 _85837 GEN_PVAR_18 s t P x).
Proof. exact (MK_COMB (@lem3270926 _85837 GEN_PVAR_18 s t P x) (@lem3270927 _85837 x)). Qed.
Lemma lem3270929 {_85837 : Type'} (GEN_PVAR_18 : _85837) (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term25 _85837 GEN_PVAR_18 s t P) = (term26 _85837 GEN_PVAR_18 s t P).
Proof. exact (fun_ext (fun x : _85837 => @lem3270928 _85837 GEN_PVAR_18 s t P x)). Qed.
Lemma lem3270930 {_85837 : Type'} : (@ex _85837) = (@ex _85837).
Proof. exact (eq_refl (@ex _85837)). Qed.
Lemma lem3270931 {_85837 : Type'} (GEN_PVAR_18 : _85837) (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term27 _85837 GEN_PVAR_18 s t P) = (term28 _85837 GEN_PVAR_18 s t P).
Proof. exact (MK_COMB (@lem3270930 _85837) (@lem3270929 _85837 GEN_PVAR_18 s t P)). Qed.
Lemma lem3270932 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term29 _85837 s t P) = (term30 _85837 s t P).
Proof. exact (fun_ext (fun GEN_PVAR_18 : _85837 => @lem3270931 _85837 GEN_PVAR_18 s t P)). Qed.
Lemma lem3270933 {_85837 : Type'} : (@GSPEC _85837) = (@GSPEC _85837).
Proof. exact (eq_refl (@GSPEC _85837)). Qed.
Lemma lem3270934 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term31 _85837 s t P) = (term1 _85837 s t P).
Proof. exact (MK_COMB (@lem3270933 _85837) (@lem3270932 _85837 s t P)). Qed.
Lemma lem3270935 {_85837 : Type'} (x : _85837) : (@IN _85837 x) = (@IN _85837 x).
Proof. exact (eq_refl (@IN _85837 x)). Qed.
Lemma lem3270936 {_85837 : Type'} (x : _85837) (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term17 _85837 x s t P) = (term32 _85837 x s t P).
Proof. exact (MK_COMB (@lem3270935 _85837 x) (@lem3270934 _85837 s t P)). Qed.
Lemma lem3270937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3270938 {_85837 : Type'} (x : _85837) (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term33 _85837 x s t P) = (term34 _85837 x s t P).
Proof. exact (MK_COMB (@lem3270937) (@lem3270936 _85837 x s t P)). Qed.
Lemma lem3270939 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term18 _85837 s t P x) = (term20 _85837 s t P x).
Proof. exact (eq_refl (term18 _85837 s t P x)). Qed.
Lemma lem3270940 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : ((term17 _85837 x s t P) = (term18 _85837 s t P x)) = ((term32 _85837 x s t P) = (term20 _85837 s t P x)).
Proof. exact (MK_COMB (@lem3270938 _85837 x s t P) (@lem3270939 _85837 s t P x)). Qed.
Lemma lem3270941 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term32 _85837 x s t P) = (term20 _85837 s t P x).
Proof. exact (EQ_MP (@lem3270940 _85837 s t P x) (@lem3270923 _85837 s t P x)). Qed.
Lemma lem3270945 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A x s t) = (term36 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3270946 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (t : _85837 -> Prop) : (term35 _85837 x s t) = (term36 _85837 s x t).
Proof. exact (@lem3270945 _85837 s x t). Qed.
Lemma lem3270950 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270951 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (@IN _85837 x P) = (P x).
Proof. exact (@lem3270950 _85837 P x). Qed.
Lemma lem3270952 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (@IN _85837 x s) = (s x).
Proof. exact (@lem3270951 _85837 s x). Qed.
Lemma lem3270953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3270954 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term37 _85837 x s) = (term38 _85837 s x).
Proof. exact (MK_COMB (@lem3270953) (@lem3270952 _85837 s x)). Qed.
Lemma lem3270956 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3270957 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (@IN _85837 x P) = (P x).
Proof. exact (@lem3270956 _85837 P x). Qed.
Lemma lem3270958 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (@IN _85837 x t) = (t x).
Proof. exact (@lem3270957 _85837 t x). Qed.
Lemma lem3270959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3270960 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (term39 _85837 x t) = (term40 _85837 t x).
Proof. exact (MK_COMB (@lem3270959) (@lem3270958 _85837 t x)). Qed.
Lemma lem3270961 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) : (term36 _85837 s x t) = (term41 _85837 s t x).
Proof. exact (MK_COMB (@lem3270954 _85837 s x) (@lem3270960 _85837 t x)). Qed.
Lemma lem3270964 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) : (term35 _85837 x s t) = (term41 _85837 s t x).
Proof. exact (TRANS (@lem3270946 _85837 s x t) (@lem3270961 _85837 s t x)). Qed.
Lemma lem3270965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3270966 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) : (term42 _85837 x s t) = (term43 _85837 s t x).
Proof. exact (MK_COMB (@lem3270965) (@lem3270964 _85837 s t x)). Qed.
Lemma lem3270967 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3270968 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term20 _85837 s t P x) = (term44 _85837 s t P x).
Proof. exact (MK_COMB (@lem3270966 _85837 s t x) (@lem3270967 _85837 P x)). Qed.
Lemma lem3270971 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term32 _85837 x s t P) = (term44 _85837 s t P x).
Proof. exact (TRANS (@lem3270941 _85837 s t P x) (@lem3270968 _85837 s t P x)). Qed.
Lemma lem3270972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3270973 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term34 _85837 x s t P) = (term45 _85837 s t P x).
Proof. exact (MK_COMB (@lem3270972) (@lem3270971 _85837 s t P x)). Qed.
Lemma lem3270975 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term35 A x s t) = (term36 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3270976 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (t : _85837 -> Prop) : (term35 _85837 x s t) = (term36 _85837 s x t).
Proof. exact (@lem3270975 _85837 s x t). Qed.
Lemma lem3270977 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term46 _85837 x s t P) = (term47 _85837 s x t P).
Proof. exact (@lem3270976 _85837 (term48 _85837 s P) x (term48 _85837 t P)). Qed.
Lemma lem3270981 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3270982 {_85837 : Type'} (p : _85837 -> Prop) (x : _85837) : (term16 _85837 x p) = (p x).
Proof. exact (@lem3270981 _85837 p x). Qed.
Lemma lem3270983 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term49 _85837 x s P) = (term50 _85837 s P x).
Proof. exact (@lem3270982 _85837 (term51 _85837 s P) x). Qed.
Lemma lem3270984 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term50 _85837 s P x) = (term52 _85837 s P x).
Proof. exact (eq_refl (term50 _85837 s P x)). Qed.
Lemma lem3270985 {_85837 : Type'} (GEN_PVAR_19 : _85837) : (@SETSPEC _85837 GEN_PVAR_19) = (@SETSPEC _85837 GEN_PVAR_19).
Proof. exact (eq_refl (@SETSPEC _85837 GEN_PVAR_19)). Qed.
Lemma lem3270986 {_85837 : Type'} (GEN_PVAR_19 : _85837) (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term53 _85837 GEN_PVAR_19 s P x) = (term54 _85837 GEN_PVAR_19 s P x).
Proof. exact (MK_COMB (@lem3270985 _85837 GEN_PVAR_19) (@lem3270984 _85837 s P x)). Qed.
Lemma lem3270987 {_85837 : Type'} (x : _85837) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3270988 {_85837 : Type'} (GEN_PVAR_19 : _85837) (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term55 _85837 GEN_PVAR_19 s P x) = (term56 _85837 GEN_PVAR_19 s P x).
Proof. exact (MK_COMB (@lem3270986 _85837 GEN_PVAR_19 s P x) (@lem3270987 _85837 x)). Qed.
Lemma lem3270989 {_85837 : Type'} (GEN_PVAR_19 : _85837) (s : _85837 -> Prop) (P : _85837 -> Prop) : (term57 _85837 GEN_PVAR_19 s P) = (term58 _85837 GEN_PVAR_19 s P).
Proof. exact (fun_ext (fun x : _85837 => @lem3270988 _85837 GEN_PVAR_19 s P x)). Qed.
Lemma lem3270990 {_85837 : Type'} : (@ex _85837) = (@ex _85837).
Proof. exact (eq_refl (@ex _85837)). Qed.
Lemma lem3270991 {_85837 : Type'} (GEN_PVAR_19 : _85837) (s : _85837 -> Prop) (P : _85837 -> Prop) : (term59 _85837 GEN_PVAR_19 s P) = (term60 _85837 GEN_PVAR_19 s P).
Proof. exact (MK_COMB (@lem3270990 _85837) (@lem3270989 _85837 GEN_PVAR_19 s P)). Qed.
Lemma lem3270992 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term61 _85837 s P) = (term62 _85837 s P).
Proof. exact (fun_ext (fun GEN_PVAR_19 : _85837 => @lem3270991 _85837 GEN_PVAR_19 s P)). Qed.
Lemma lem3270993 {_85837 : Type'} : (@GSPEC _85837) = (@GSPEC _85837).
Proof. exact (eq_refl (@GSPEC _85837)). Qed.
Lemma lem3270994 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term63 _85837 s P) = (term48 _85837 s P).
Proof. exact (MK_COMB (@lem3270993 _85837) (@lem3270992 _85837 s P)). Qed.
Lemma lem3270995 {_85837 : Type'} (x : _85837) : (@IN _85837 x) = (@IN _85837 x).
Proof. exact (eq_refl (@IN _85837 x)). Qed.
Lemma lem3270996 {_85837 : Type'} (x : _85837) (s : _85837 -> Prop) (P : _85837 -> Prop) : (term49 _85837 x s P) = (term64 _85837 x s P).
Proof. exact (MK_COMB (@lem3270995 _85837 x) (@lem3270994 _85837 s P)). Qed.
Lemma lem3270997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3270998 {_85837 : Type'} (x : _85837) (s : _85837 -> Prop) (P : _85837 -> Prop) : (term65 _85837 x s P) = (term66 _85837 x s P).
Proof. exact (MK_COMB (@lem3270997) (@lem3270996 _85837 x s P)). Qed.
Lemma lem3270999 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term50 _85837 s P x) = (term52 _85837 s P x).
Proof. exact (eq_refl (term50 _85837 s P x)). Qed.
Lemma lem3271000 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : ((term49 _85837 x s P) = (term50 _85837 s P x)) = ((term64 _85837 x s P) = (term52 _85837 s P x)).
Proof. exact (MK_COMB (@lem3270998 _85837 x s P) (@lem3270999 _85837 s P x)). Qed.
Lemma lem3271001 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term64 _85837 x s P) = (term52 _85837 s P x).
Proof. exact (EQ_MP (@lem3271000 _85837 s P x) (@lem3270983 _85837 s P x)). Qed.
Lemma lem3271005 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3271006 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (@IN _85837 x P) = (P x).
Proof. exact (@lem3271005 _85837 P x). Qed.
Lemma lem3271007 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (@IN _85837 x s) = (s x).
Proof. exact (@lem3271006 _85837 s x). Qed.
Lemma lem3271008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3271009 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term37 _85837 x s) = (term38 _85837 s x).
Proof. exact (MK_COMB (@lem3271008) (@lem3271007 _85837 s x)). Qed.
Lemma lem3271010 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3271011 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term52 _85837 s P x) = (term67 _85837 s P x).
Proof. exact (MK_COMB (@lem3271009 _85837 s x) (@lem3271010 _85837 P x)). Qed.
Lemma lem3271014 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term64 _85837 x s P) = (term67 _85837 s P x).
Proof. exact (TRANS (@lem3271001 _85837 s P x) (@lem3271011 _85837 s P x)). Qed.
Lemma lem3271015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3271016 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term68 _85837 x s P) = (term69 _85837 s P x).
Proof. exact (MK_COMB (@lem3271015) (@lem3271014 _85837 s P x)). Qed.
Lemma lem3271018 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3271019 {_85837 : Type'} (p : _85837 -> Prop) (x : _85837) : (term16 _85837 x p) = (p x).
Proof. exact (@lem3271018 _85837 p x). Qed.
Lemma lem3271020 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term49 _85837 x t P) = (term50 _85837 t P x).
Proof. exact (@lem3271019 _85837 (term51 _85837 t P) x). Qed.
Lemma lem3271021 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term50 _85837 t P x) = (term52 _85837 t P x).
Proof. exact (eq_refl (term50 _85837 t P x)). Qed.
Lemma lem3271022 {_85837 : Type'} (GEN_PVAR_20 : _85837) : (@SETSPEC _85837 GEN_PVAR_20) = (@SETSPEC _85837 GEN_PVAR_20).
Proof. exact (eq_refl (@SETSPEC _85837 GEN_PVAR_20)). Qed.
Lemma lem3271023 {_85837 : Type'} (GEN_PVAR_20 : _85837) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term53 _85837 GEN_PVAR_20 t P x) = (term54 _85837 GEN_PVAR_20 t P x).
Proof. exact (MK_COMB (@lem3271022 _85837 GEN_PVAR_20) (@lem3271021 _85837 t P x)). Qed.
Lemma lem3271024 {_85837 : Type'} (x : _85837) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3271025 {_85837 : Type'} (GEN_PVAR_20 : _85837) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term55 _85837 GEN_PVAR_20 t P x) = (term56 _85837 GEN_PVAR_20 t P x).
Proof. exact (MK_COMB (@lem3271023 _85837 GEN_PVAR_20 t P x) (@lem3271024 _85837 x)). Qed.
Lemma lem3271026 {_85837 : Type'} (GEN_PVAR_20 : _85837) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term57 _85837 GEN_PVAR_20 t P) = (term58 _85837 GEN_PVAR_20 t P).
Proof. exact (fun_ext (fun x : _85837 => @lem3271025 _85837 GEN_PVAR_20 t P x)). Qed.
Lemma lem3271027 {_85837 : Type'} : (@ex _85837) = (@ex _85837).
Proof. exact (eq_refl (@ex _85837)). Qed.
Lemma lem3271028 {_85837 : Type'} (GEN_PVAR_20 : _85837) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term59 _85837 GEN_PVAR_20 t P) = (term60 _85837 GEN_PVAR_20 t P).
Proof. exact (MK_COMB (@lem3271027 _85837) (@lem3271026 _85837 GEN_PVAR_20 t P)). Qed.
Lemma lem3271029 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) : (term61 _85837 t P) = (term62 _85837 t P).
Proof. exact (fun_ext (fun GEN_PVAR_20 : _85837 => @lem3271028 _85837 GEN_PVAR_20 t P)). Qed.
Lemma lem3271030 {_85837 : Type'} : (@GSPEC _85837) = (@GSPEC _85837).
Proof. exact (eq_refl (@GSPEC _85837)). Qed.
Lemma lem3271031 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) : (term63 _85837 t P) = (term48 _85837 t P).
Proof. exact (MK_COMB (@lem3271030 _85837) (@lem3271029 _85837 t P)). Qed.
Lemma lem3271032 {_85837 : Type'} (x : _85837) : (@IN _85837 x) = (@IN _85837 x).
Proof. exact (eq_refl (@IN _85837 x)). Qed.
Lemma lem3271033 {_85837 : Type'} (x : _85837) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term49 _85837 x t P) = (term64 _85837 x t P).
Proof. exact (MK_COMB (@lem3271032 _85837 x) (@lem3271031 _85837 t P)). Qed.
Lemma lem3271034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3271035 {_85837 : Type'} (x : _85837) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term65 _85837 x t P) = (term66 _85837 x t P).
Proof. exact (MK_COMB (@lem3271034) (@lem3271033 _85837 x t P)). Qed.
Lemma lem3271036 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term50 _85837 t P x) = (term52 _85837 t P x).
Proof. exact (eq_refl (term50 _85837 t P x)). Qed.
Lemma lem3271037 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : ((term49 _85837 x t P) = (term50 _85837 t P x)) = ((term64 _85837 x t P) = (term52 _85837 t P x)).
Proof. exact (MK_COMB (@lem3271035 _85837 x t P) (@lem3271036 _85837 t P x)). Qed.
Lemma lem3271038 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term64 _85837 x t P) = (term52 _85837 t P x).
Proof. exact (EQ_MP (@lem3271037 _85837 t P x) (@lem3271020 _85837 t P x)). Qed.
Lemma lem3271042 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3271043 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (@IN _85837 x P) = (P x).
Proof. exact (@lem3271042 _85837 P x). Qed.
Lemma lem3271044 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (@IN _85837 x t) = (t x).
Proof. exact (@lem3271043 _85837 t x). Qed.
Lemma lem3271045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3271046 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (term37 _85837 x t) = (term38 _85837 t x).
Proof. exact (MK_COMB (@lem3271045) (@lem3271044 _85837 t x)). Qed.
Lemma lem3271047 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3271048 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term52 _85837 t P x) = (term67 _85837 t P x).
Proof. exact (MK_COMB (@lem3271046 _85837 t x) (@lem3271047 _85837 P x)). Qed.
Lemma lem3271051 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term64 _85837 x t P) = (term67 _85837 t P x).
Proof. exact (TRANS (@lem3271038 _85837 t P x) (@lem3271048 _85837 t P x)). Qed.
Lemma lem3271052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3271053 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term70 _85837 x t P) = (term71 _85837 t P x).
Proof. exact (MK_COMB (@lem3271052) (@lem3271051 _85837 t P x)). Qed.
Lemma lem3271054 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term47 _85837 s x t P) = (term72 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271016 _85837 s P x) (@lem3271053 _85837 t P x)). Qed.
Lemma lem3271057 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term46 _85837 x s t P) = (term72 _85837 s t P x).
Proof. exact (TRANS (@lem3270977 _85837 s x t P) (@lem3271054 _85837 s t P x)). Qed.
Lemma lem3271058 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : ((term32 _85837 x s t P) = (term46 _85837 x s t P)) = ((term44 _85837 s t P x) = (term72 _85837 s t P x)).
Proof. exact (MK_COMB (@lem3270973 _85837 s t P x) (@lem3271057 _85837 s t P x)). Qed.
Lemma lem3271061 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term73 _85837 s t P) = (term74 _85837 s t P).
Proof. exact (fun_ext (fun x : _85837 => @lem3271058 _85837 s t P x)). Qed.
Lemma lem3271062 {_85837 : Type'} : (@all _85837) = (@all _85837).
Proof. exact (eq_refl (@all _85837)). Qed.
Lemma lem3271063 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term3 _85837 s t P) = (term75 _85837 s t P).
Proof. exact (MK_COMB (@lem3271062 _85837) (@lem3271061 _85837 s t P)). Qed.
Lemma lem3271068 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term5 _85837 s P) = (term76 _85837 s P).
Proof. exact (fun_ext (fun t : _85837 -> Prop => @lem3271063 _85837 s t P)). Qed.
Lemma lem3271069 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3271070 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term7 _85837 s P) = (term77 _85837 s P).
Proof. exact (MK_COMB (@lem3271069 _85837) (@lem3271068 _85837 s P)). Qed.
Lemma lem3271075 {_85837 : Type'} (P : _85837 -> Prop) : (term9 _85837 P) = (term78 _85837 P).
Proof. exact (fun_ext (fun s : _85837 -> Prop => @lem3271070 _85837 s P)). Qed.
Lemma lem3271076 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3271077 {_85837 : Type'} (P : _85837 -> Prop) : (term11 _85837 P) = (term79 _85837 P).
Proof. exact (MK_COMB (@lem3271076 _85837) (@lem3271075 _85837 P)). Qed.
Lemma lem3271082 {_85837 : Type'} : (term13 _85837) = (term80 _85837).
Proof. exact (fun_ext (fun P : _85837 -> Prop => @lem3271077 _85837 P)). Qed.
Lemma lem3271083 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3271084 {_85837 : Type'} : (term15 _85837) = (term81 _85837).
Proof. exact (MK_COMB (@lem3271083 _85837) (@lem3271082 _85837)). Qed.
Lemma lem3271089 {_85837 : Type'} : (term81 _85837) = (term15 _85837).
Proof. exact (SYM (@lem3271084 _85837)). Qed.
Lemma lem3271091 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3271092 {_85837 : Type'} : (term81 _85837) = (term83 _85837).
Proof. exact (@lem3271091 (term81 _85837)). Qed.
Lemma lem3271093 {_85837 : Type'} : (term83 _85837) = (term81 _85837).
Proof. exact (SYM (@lem3271092 _85837)). Qed.
Lemma lem3271094 {_85837 : Type'} (h1 : term84 _85837) : term84 _85837.
Proof. exact (h1). Qed.
Lemma lem3271097 {_85837 : Type'} (h1 : term83 _85837) : term83 _85837.
Proof. exact (h1). Qed.
Lemma lem3271098 {_85837 : Type'} : term85 _85837.
Proof. exact (fun h0 : term83 _85837 => @lem3271097 _85837 h0). Qed.
Lemma lem3271099 {_85837 : Type'} (h1 : term85 _85837) : term85 _85837.
Proof. exact (h1). Qed.
Lemma lem3271100 {_85837 : Type'} (h1 : term83 _85837) : term83 _85837.
Proof. exact (h1). Qed.
Lemma lem3271101 {_85837 : Type'} (h1 : term83 _85837) (h2 : term85 _85837) : term83 _85837.
Proof. exact (@lem3271099 _85837 h2 (@lem3271100 _85837 h1)). Qed.
Lemma lem3271102 {_85837 : Type'} (h1 : term83 _85837) : term86 _85837.
Proof. exact (fun h0 : term85 _85837 => @lem3271101 _85837 h1 h0). Qed.
Lemma lem3271103 {_85837 : Type'} (h1 : term85 _85837) : term85 _85837.
Proof. exact (h1). Qed.
Lemma lem3271104 {_85837 : Type'} (h1 : term83 _85837) (h2 : term85 _85837) : term83 _85837.
Proof. exact (@lem3271102 _85837 h1 (@lem3271103 _85837 h2)). Qed.
Lemma lem3271105 {_85837 : Type'} (h1 : term85 _85837) : term85 _85837.
Proof. exact (fun h0 : term83 _85837 => @lem3271104 _85837 h0 h1). Qed.
Lemma lem3271106 {_85837 : Type'} : term87 _85837.
Proof. exact (fun h0 : term85 _85837 => @lem3271105 _85837 h0). Qed.
Lemma lem3271109 {_85837 : Type'} : term85 _85837.
Proof. exact (@lem3271106 _85837 (@lem3271098 _85837)). Qed.
Lemma lem3271110 {_85837 : Type'} : term85 _85837.
Proof. exact (@lem3271109 _85837). Qed.
Lemma lem3271112 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3271113 {_85837 : Type'} : (term83 _85837) = (term88 _85837).
Proof. exact (@lem3271112 (term84 _85837)). Qed.
Lemma lem3271115 (t : Prop) : (term89 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3271116 {_85837 : Type'} : (term88 _85837) = (term81 _85837).
Proof. exact (@lem3271115 (term81 _85837)). Qed.
Lemma lem3271147 {_85837 : Type'} : (term83 _85837) = (term81 _85837).
Proof. exact (TRANS (@lem3271113 _85837) (@lem3271116 _85837)). Qed.
Lemma lem3271176 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : ((term44 _85837 s t P x) = (term72 _85837 s t P x)) = ((term44 _85837 s t P x) = (term72 _85837 s t P x)).
Proof. exact (eq_refl ((term44 _85837 s t P x) = (term72 _85837 s t P x))). Qed.
Lemma lem3271177 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term74 _85837 s t P) = (term74 _85837 s t P).
Proof. exact (fun_ext (fun x : _85837 => @lem3271176 _85837 s t P x)). Qed.
Lemma lem3271178 {_85837 : Type'} : (@all _85837) = (@all _85837).
Proof. exact (eq_refl (@all _85837)). Qed.
Lemma lem3271179 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : (term75 _85837 s t P) = (term75 _85837 s t P).
Proof. exact (MK_COMB (@lem3271178 _85837) (@lem3271177 _85837 s t P)). Qed.
Lemma lem3271180 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term76 _85837 s P) = (term76 _85837 s P).
Proof. exact (fun_ext (fun t : _85837 -> Prop => @lem3271179 _85837 s t P)). Qed.
Lemma lem3271181 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3271182 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : (term77 _85837 s P) = (term77 _85837 s P).
Proof. exact (MK_COMB (@lem3271181 _85837) (@lem3271180 _85837 s P)). Qed.
Lemma lem3271183 {_85837 : Type'} (P : _85837 -> Prop) : (term78 _85837 P) = (term78 _85837 P).
Proof. exact (fun_ext (fun s : _85837 -> Prop => @lem3271182 _85837 s P)). Qed.
Lemma lem3271184 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3271185 {_85837 : Type'} (P : _85837 -> Prop) : (term79 _85837 P) = (term79 _85837 P).
Proof. exact (MK_COMB (@lem3271184 _85837) (@lem3271183 _85837 P)). Qed.
Lemma lem3271186 {_85837 : Type'} : (term80 _85837) = (term80 _85837).
Proof. exact (fun_ext (fun P : _85837 -> Prop => @lem3271185 _85837 P)). Qed.
Lemma lem3271187 {_85837 : Type'} : (@all (_85837 -> Prop)) = (@all (_85837 -> Prop)).
Proof. exact (eq_refl (@all (_85837 -> Prop))). Qed.
Lemma lem3271188 {_85837 : Type'} : (term81 _85837) = (term81 _85837).
Proof. exact (MK_COMB (@lem3271187 _85837) (@lem3271186 _85837)). Qed.
Lemma lem3271225 {_85837 : Type'} : (term83 _85837) = (term81 _85837).
Proof. exact (TRANS (@lem3271147 _85837) (@lem3271188 _85837)). Qed.
Lemma lem3271226 {_85837 : Type'} : (term81 _85837) = (term83 _85837).
Proof. exact (SYM (@lem3271225 _85837)). Qed.
Lemma lem3271228 (p : Prop) : p = (term82 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3271229 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : ((term44 _85837 s t P x) = (term72 _85837 s t P x)) = (term90 _85837 s t P x).
Proof. exact (@lem3271228 ((term44 _85837 s t P x) = (term72 _85837 s t P x))). Qed.
Lemma lem3271230 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term90 _85837 s t P x) = ((term44 _85837 s t P x) = (term72 _85837 s t P x)).
Proof. exact (SYM (@lem3271229 _85837 s t P x)). Qed.
Lemma lem3271231 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term91 _85837 s t P x) : term91 _85837 s t P x.
Proof. exact (h1). Qed.
Lemma lem3271237 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (term92 _85837 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3271239 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term93 _85837 s x) = (term93 _85837 s x).
Proof. exact (eq_refl (term93 _85837 s x)). Qed.
Lemma lem3271240 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) : (term94 _85837 s t x) = (term95 _85837 s t x).
Proof. exact (MK_COMB (@lem3271239 _85837 s x) (@lem3271237 _85837 t x)). Qed.
Lemma lem3271241 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) : (term96 _85837 s t x) = (term94 _85837 s t x).
Proof. exact (@lem17045 (s x) (term40 _85837 t x)). Qed.
Lemma lem3271242 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) : (term96 _85837 s t x) = (term95 _85837 s t x).
Proof. exact (TRANS (@lem3271241 _85837 s t x) (@lem3271240 _85837 s t x)). Qed.
Lemma lem3271246 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term40 _85837 P x) = (term40 _85837 P x).
Proof. exact (eq_refl (term40 _85837 P x)). Qed.
Lemma lem3271248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3271249 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) : (term97 _85837 s t x) = (term98 _85837 s t x).
Proof. exact (MK_COMB (@lem3271248) (@lem3271242 _85837 s t x)). Qed.
Lemma lem3271250 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term99 _85837 s t P x) = (term100 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271249 _85837 s t x) (@lem3271246 _85837 P x)). Qed.
Lemma lem3271251 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term101 _85837 s t P x) = (term99 _85837 s t P x).
Proof. exact (@lem17045 (term41 _85837 s t x) (P x)). Qed.
Lemma lem3271252 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term101 _85837 s t P x) = (term100 _85837 s t P x).
Proof. exact (TRANS (@lem3271251 _85837 s t P x) (@lem3271250 _85837 s t P x)). Qed.
Lemma lem3271264 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term71 _85837 s P x) = (term102 _85837 s P x).
Proof. exact (@lem17045 (s x) (P x)). Qed.
Lemma lem3271276 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term71 _85837 t P x) = (term102 _85837 t P x).
Proof. exact (@lem17045 (t x) (P x)). Qed.
Lemma lem3271281 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term103 _85837 t P x) = (term67 _85837 t P x).
Proof. exact (@lem16933 (term67 _85837 t P x)). Qed.
Lemma lem3271282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3271283 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term104 _85837 s P x) = (term105 _85837 s P x).
Proof. exact (MK_COMB (@lem3271282) (@lem3271264 _85837 s P x)). Qed.
Lemma lem3271284 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term106 _85837 s t P x) = (term107 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271283 _85837 s P x) (@lem3271281 _85837 t P x)). Qed.
Lemma lem3271285 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term108 _85837 s t P x) = (term106 _85837 s t P x).
Proof. exact (@lem17045 (term67 _85837 s P x) (term71 _85837 t P x)). Qed.
Lemma lem3271286 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term108 _85837 s t P x) = (term107 _85837 s t P x).
Proof. exact (TRANS (@lem3271285 _85837 s t P x) (@lem3271284 _85837 s t P x)). Qed.
Lemma lem3271288 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term69 _85837 s P x) = (term69 _85837 s P x).
Proof. exact (eq_refl (term69 _85837 s P x)). Qed.
Lemma lem3271289 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term72 _85837 s t P x) = (term109 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271288 _85837 s P x) (@lem3271276 _85837 t P x)). Qed.
Lemma lem3271290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3271291 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term110 _85837 s t P x) = (term111 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271290) (@lem3271252 _85837 s t P x)). Qed.
Lemma lem3271292 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term112 _85837 s t P x) = (term113 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271291 _85837 s t P x) (@lem3271289 _85837 s t P x)). Qed.
Lemma lem3271294 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term114 _85837 s t P x) = (term114 _85837 s t P x).
Proof. exact (eq_refl (term114 _85837 s t P x)). Qed.
Lemma lem3271295 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term115 _85837 s t P x) = (term116 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271294 _85837 s t P x) (@lem3271286 _85837 s t P x)). Qed.
Lemma lem3271296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3271297 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term117 _85837 s t P x) = (term118 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271296) (@lem3271295 _85837 s t P x)). Qed.
Lemma lem3271298 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term119 _85837 s t P x) = (term120 _85837 s t P x).
Proof. exact (MK_COMB (@lem3271297 _85837 s t P x) (@lem3271292 _85837 s t P x)). Qed.
Lemma lem3271299 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term91 _85837 s t P x) = (term119 _85837 s t P x).
Proof. exact (@lem17646 (term44 _85837 s t P x) (term72 _85837 s t P x)). Qed.
Lemma lem3271304 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term91 _85837 s t P x) = (term120 _85837 s t P x).
Proof. exact (TRANS (@lem3271299 _85837 s t P x) (@lem3271298 _85837 s t P x)). Qed.
Lemma lem3271401 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term91 _85837 s t P x) : term120 _85837 s t P x.
Proof. exact (EQ_MP (@lem3271304 _85837 s t P x) (@lem3271231 _85837 s t P x h1)). Qed.
Lemma lem3271402 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term116 _85837 s t P x.
Proof. exact (h1). Qed.
Lemma lem3271403 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term113 _85837 s t P x.
Proof. exact (h1). Qed.
Lemma lem3271404 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term107 _85837 s t P x.
Proof. exact (proj2 (@lem3271402 _85837 s t P x h1)). Qed.
Lemma lem3271405 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term44 _85837 s t P x.
Proof. exact (proj1 (@lem3271402 _85837 s t P x h1)). Qed.
Lemma lem3271407 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term41 _85837 s t x.
Proof. exact (proj1 (@lem3271405 _85837 s t P x h1)). Qed.
Lemma lem3271410 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term102 _85837 s P x) : term102 _85837 s P x.
Proof. exact (h1). Qed.
Lemma lem3271411 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term67 _85837 t P x) : term67 _85837 t P x.
Proof. exact (h1). Qed.
Lemma lem3271416 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term109 _85837 s t P x.
Proof. exact (proj2 (@lem3271403 _85837 s t P x h1)). Qed.
Lemma lem3271417 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term100 _85837 s t P x.
Proof. exact (proj1 (@lem3271403 _85837 s t P x h1)). Qed.
Lemma lem3271418 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term102 _85837 t P x.
Proof. exact (proj2 (@lem3271416 _85837 s t P x h1)). Qed.
Lemma lem3271419 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term67 _85837 s P x.
Proof. exact (proj1 (@lem3271416 _85837 s t P x h1)). Qed.
Lemma lem3271424 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) (h1 : term95 _85837 s t x) : term95 _85837 s t x.
Proof. exact (h1). Qed.
Lemma lem3271428 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) (h1 : term95 _85837 s t x) : term95 _85837 s t x.
Proof. exact (h1). Qed.
Lemma lem3271447 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term40 _85837 s x.
Proof. exact (h1). Qed.
Lemma lem3271463 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271499 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term40 _85837 s x.
Proof. exact (h1). Qed.
Lemma lem3271511 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) : term40 _85837 t x.
Proof. exact (h1). Qed.
Lemma lem3271515 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3271531 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271547 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term40 _85837 s x.
Proof. exact (h1). Qed.
Lemma lem3271559 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271575 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271579 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271587 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term40 _85837 s x.
Proof. exact (h1). Qed.
Lemma lem3271595 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271601 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term40 _85837 t x.
Proof. exact (proj2 (@lem3271407 _85837 s t P x h1)). Qed.
Lemma lem3271613 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term40 _85837 s x.
Proof. exact (h1). Qed.
Lemma lem3271619 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) : term40 _85837 t x.
Proof. exact (h1). Qed.
Lemma lem3271621 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3271629 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271637 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term40 _85837 s x.
Proof. exact (h1). Qed.
Lemma lem3271643 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271651 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271653 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term40 _85837 P x.
Proof. exact (h1). Qed.
Lemma lem3271655 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : s x.
Proof. exact (proj1 (@lem3271407 _85837 s t P x h1)). Qed.
Lemma lem3271656 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term121 _85837 s x.
Proof. exact (fun h0 : term40 _85837 s x => @lem3271655 _85837 s t P x h1). Qed.
Lemma lem3271658 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271659 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term121 _85837 s x) = (s x).
Proof. exact (@lem3271658 (s x)). Qed.
Lemma lem3271660 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : s x.
Proof. exact (EQ_MP (@lem3271659 _85837 s x) (@lem3271656 _85837 s t P x h1)). Qed.
Lemma lem3271663 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271665 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term40 _85837 s x) = (term123 _85837 s x).
Proof. exact (@lem3271663 (s x)). Qed.
Lemma lem3271668 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term123 _85837 s x.
Proof. exact (EQ_MP (@lem3271665 _85837 s x) (@lem3271587 _85837 s x h1)). Qed.
Lemma lem3271671 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (@lem3271668 _85837 s x h1 (@lem3271660 _85837 s t P x h2)). Qed.
Lemma lem3271672 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271671 _85837 s t P x h1 h2). Qed.
Lemma lem3271674 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271675 : term124 = False.
Proof. exact (@lem3271674 False). Qed.
Lemma lem3271676 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271675) (@lem3271672 _85837 s t P x h1 h2)). Qed.
Lemma lem3271678 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : P x.
Proof. exact (proj2 (@lem3271405 _85837 s t P x h1)). Qed.
Lemma lem3271679 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term121 _85837 P x.
Proof. exact (fun h0 : term40 _85837 P x => @lem3271678 _85837 s t P x h1). Qed.
Lemma lem3271681 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271682 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term121 _85837 P x) = (P x).
Proof. exact (@lem3271681 (P x)). Qed.
Lemma lem3271683 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : P x.
Proof. exact (EQ_MP (@lem3271682 _85837 P x) (@lem3271679 _85837 s t P x h1)). Qed.
Lemma lem3271686 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271688 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term40 _85837 P x) = (term123 _85837 P x).
Proof. exact (@lem3271686 (P x)). Qed.
Lemma lem3271691 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term123 _85837 P x.
Proof. exact (EQ_MP (@lem3271688 _85837 P x) (@lem3271595 _85837 P x h1)). Qed.
Lemma lem3271694 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (@lem3271691 _85837 P x h1 (@lem3271683 _85837 s t P x h2)). Qed.
Lemma lem3271695 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271694 _85837 s t P x h1 h2). Qed.
Lemma lem3271697 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271698 : term124 = False.
Proof. exact (@lem3271697 False). Qed.
Lemma lem3271699 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271698) (@lem3271695 _85837 s t P x h1 h2)). Qed.
Lemma lem3271701 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term67 _85837 t P x) : t x.
Proof. exact (proj1 (@lem3271411 _85837 t P x h1)). Qed.
Lemma lem3271702 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term67 _85837 t P x) : term121 _85837 t x.
Proof. exact (fun h0 : term40 _85837 t x => @lem3271701 _85837 t P x h1). Qed.
Lemma lem3271704 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271705 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (term121 _85837 t x) = (t x).
Proof. exact (@lem3271704 (t x)). Qed.
Lemma lem3271706 {_85837 : Type'} (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term67 _85837 t P x) : t x.
Proof. exact (EQ_MP (@lem3271705 _85837 t x) (@lem3271702 _85837 t P x h1)). Qed.
Lemma lem3271709 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271711 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (term40 _85837 t x) = (term123 _85837 t x).
Proof. exact (@lem3271709 (t x)). Qed.
Lemma lem3271714 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : term123 _85837 t x.
Proof. exact (EQ_MP (@lem3271711 _85837 t x) (@lem3271601 _85837 s t P x h1)). Qed.
Lemma lem3271717 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term67 _85837 t P x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (@lem3271714 _85837 s t P x h2 (@lem3271706 _85837 t P x h1)). Qed.
Lemma lem3271718 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term67 _85837 t P x) (h2 : term116 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271717 _85837 s t P x h1 h2). Qed.
Lemma lem3271720 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271721 : term124 = False.
Proof. exact (@lem3271720 False). Qed.
Lemma lem3271722 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term67 _85837 t P x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271721) (@lem3271718 _85837 s t P x h1 h2)). Qed.
Lemma lem3271724 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : s x.
Proof. exact (proj1 (@lem3271419 _85837 s t P x h1)). Qed.
Lemma lem3271725 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term121 _85837 s x.
Proof. exact (fun h0 : term40 _85837 s x => @lem3271724 _85837 s t P x h1). Qed.
Lemma lem3271727 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271728 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term121 _85837 s x) = (s x).
Proof. exact (@lem3271727 (s x)). Qed.
Lemma lem3271729 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : s x.
Proof. exact (EQ_MP (@lem3271728 _85837 s x) (@lem3271725 _85837 s t P x h1)). Qed.
Lemma lem3271732 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271734 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term40 _85837 s x) = (term123 _85837 s x).
Proof. exact (@lem3271732 (s x)). Qed.
Lemma lem3271737 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term123 _85837 s x.
Proof. exact (EQ_MP (@lem3271734 _85837 s x) (@lem3271613 _85837 s x h1)). Qed.
Lemma lem3271740 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (@lem3271737 _85837 s x h1 (@lem3271729 _85837 s t P x h2)). Qed.
Lemma lem3271741 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271740 _85837 s t P x h1 h2). Qed.
Lemma lem3271743 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271744 : term124 = False.
Proof. exact (@lem3271743 False). Qed.
Lemma lem3271745 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271744) (@lem3271741 _85837 s t P x h1 h2)). Qed.
Lemma lem3271747 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3271748 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : t x) : term121 _85837 t x.
Proof. exact (fun h0 : term40 _85837 t x => @lem3271747 _85837 t x h1). Qed.
Lemma lem3271750 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271751 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (term121 _85837 t x) = (t x).
Proof. exact (@lem3271750 (t x)). Qed.
Lemma lem3271752 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3271751 _85837 t x) (@lem3271748 _85837 t x h1)). Qed.
Lemma lem3271755 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271757 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) : (term40 _85837 t x) = (term123 _85837 t x).
Proof. exact (@lem3271755 (t x)). Qed.
Lemma lem3271760 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) : term123 _85837 t x.
Proof. exact (EQ_MP (@lem3271757 _85837 t x) (@lem3271619 _85837 t x h1)). Qed.
Lemma lem3271763 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (@lem3271760 _85837 t x h1 (@lem3271752 _85837 t x h2)). Qed.
Lemma lem3271764 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271763 _85837 t x h1 h2). Qed.
Lemma lem3271766 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271767 : term124 = False.
Proof. exact (@lem3271766 False). Qed.
Lemma lem3271768 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3271767) (@lem3271764 _85837 t x h1 h2)). Qed.
Lemma lem3271770 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : P x.
Proof. exact (proj2 (@lem3271419 _85837 s t P x h1)). Qed.
Lemma lem3271771 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term121 _85837 P x.
Proof. exact (fun h0 : term40 _85837 P x => @lem3271770 _85837 s t P x h1). Qed.
Lemma lem3271773 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271774 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term121 _85837 P x) = (P x).
Proof. exact (@lem3271773 (P x)). Qed.
Lemma lem3271775 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : P x.
Proof. exact (EQ_MP (@lem3271774 _85837 P x) (@lem3271771 _85837 s t P x h1)). Qed.
Lemma lem3271778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271780 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term40 _85837 P x) = (term123 _85837 P x).
Proof. exact (@lem3271778 (P x)). Qed.
Lemma lem3271783 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term123 _85837 P x.
Proof. exact (EQ_MP (@lem3271780 _85837 P x) (@lem3271629 _85837 P x h1)). Qed.
Lemma lem3271786 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (@lem3271783 _85837 P x h1 (@lem3271775 _85837 s t P x h2)). Qed.
Lemma lem3271787 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271786 _85837 s t P x h1 h2). Qed.
Lemma lem3271789 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271790 : term124 = False.
Proof. exact (@lem3271789 False). Qed.
Lemma lem3271791 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271790) (@lem3271787 _85837 s t P x h1 h2)). Qed.
Lemma lem3271793 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : s x.
Proof. exact (proj1 (@lem3271419 _85837 s t P x h1)). Qed.
Lemma lem3271794 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term121 _85837 s x.
Proof. exact (fun h0 : term40 _85837 s x => @lem3271793 _85837 s t P x h1). Qed.
Lemma lem3271796 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271797 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term121 _85837 s x) = (s x).
Proof. exact (@lem3271796 (s x)). Qed.
Lemma lem3271798 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : s x.
Proof. exact (EQ_MP (@lem3271797 _85837 s x) (@lem3271794 _85837 s t P x h1)). Qed.
Lemma lem3271801 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271803 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) : (term40 _85837 s x) = (term123 _85837 s x).
Proof. exact (@lem3271801 (s x)). Qed.
Lemma lem3271806 {_85837 : Type'} (s : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) : term123 _85837 s x.
Proof. exact (EQ_MP (@lem3271803 _85837 s x) (@lem3271637 _85837 s x h1)). Qed.
Lemma lem3271809 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (@lem3271806 _85837 s x h1 (@lem3271798 _85837 s t P x h2)). Qed.
Lemma lem3271810 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271809 _85837 s t P x h1 h2). Qed.
Lemma lem3271812 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271813 : term124 = False.
Proof. exact (@lem3271812 False). Qed.
Lemma lem3271814 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271813) (@lem3271810 _85837 s t P x h1 h2)). Qed.
Lemma lem3271816 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : P x.
Proof. exact (proj2 (@lem3271419 _85837 s t P x h1)). Qed.
Lemma lem3271817 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term121 _85837 P x.
Proof. exact (fun h0 : term40 _85837 P x => @lem3271816 _85837 s t P x h1). Qed.
Lemma lem3271819 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271820 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term121 _85837 P x) = (P x).
Proof. exact (@lem3271819 (P x)). Qed.
Lemma lem3271821 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : P x.
Proof. exact (EQ_MP (@lem3271820 _85837 P x) (@lem3271817 _85837 s t P x h1)). Qed.
Lemma lem3271824 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271826 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term40 _85837 P x) = (term123 _85837 P x).
Proof. exact (@lem3271824 (P x)). Qed.
Lemma lem3271829 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term123 _85837 P x.
Proof. exact (EQ_MP (@lem3271826 _85837 P x) (@lem3271643 _85837 P x h1)). Qed.
Lemma lem3271832 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (@lem3271829 _85837 P x h1 (@lem3271821 _85837 s t P x h2)). Qed.
Lemma lem3271833 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271832 _85837 s t P x h1 h2). Qed.
Lemma lem3271835 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271836 : term124 = False.
Proof. exact (@lem3271835 False). Qed.
Lemma lem3271837 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271836) (@lem3271833 _85837 s t P x h1 h2)). Qed.
Lemma lem3271839 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : P x.
Proof. exact (proj2 (@lem3271419 _85837 s t P x h1)). Qed.
Lemma lem3271840 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : term121 _85837 P x.
Proof. exact (fun h0 : term40 _85837 P x => @lem3271839 _85837 s t P x h1). Qed.
Lemma lem3271842 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271843 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term121 _85837 P x) = (P x).
Proof. exact (@lem3271842 (P x)). Qed.
Lemma lem3271844 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : P x.
Proof. exact (EQ_MP (@lem3271843 _85837 P x) (@lem3271840 _85837 s t P x h1)). Qed.
Lemma lem3271847 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3271849 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) : (term40 _85837 P x) = (term123 _85837 P x).
Proof. exact (@lem3271847 (P x)). Qed.
Lemma lem3271852 {_85837 : Type'} (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) : term123 _85837 P x.
Proof. exact (EQ_MP (@lem3271849 _85837 P x) (@lem3271651 _85837 P x h1)). Qed.
Lemma lem3271855 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (@lem3271852 _85837 P x h1 (@lem3271844 _85837 s t P x h2)). Qed.
Lemma lem3271856 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : term124.
Proof. exact (fun h0 : ~ False => @lem3271855 _85837 s t P x h1 h2). Qed.
Lemma lem3271858 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3271859 : term124 = False.
Proof. exact (@lem3271858 False). Qed.
Lemma lem3271860 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271859) (@lem3271856 _85837 s t P x h1 h2)). Qed.
Lemma lem3271861 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271860 _85837 s t P x h1 h2) (fun h3 : False => @lem3271653 _85837 P x h1)). Qed.
Lemma lem3271862 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271861 _85837 s t P x h1 h2) (@lem3271653 _85837 P x h1)). Qed.
Lemma lem3271863 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271862 _85837 s t P x h1 h2) (fun h3 : False => @lem3271651 _85837 P x h1)). Qed.
Lemma lem3271864 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271863 _85837 s t P x h1 h2) (@lem3271651 _85837 P x h1)). Qed.
Lemma lem3271865 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271837 _85837 s t P x h1 h2) (fun h3 : False => @lem3271643 _85837 P x h1)). Qed.
Lemma lem3271866 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271865 _85837 s t P x h1 h2) (@lem3271643 _85837 P x h1)). Qed.
Lemma lem3271867 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271814 _85837 s t P x h1 h2) (fun h3 : False => @lem3271637 _85837 s x h1)). Qed.
Lemma lem3271868 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271867 _85837 s t P x h1 h2) (@lem3271637 _85837 s x h1)). Qed.
Lemma lem3271869 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271791 _85837 s t P x h1 h2) (fun h3 : False => @lem3271629 _85837 P x h1)). Qed.
Lemma lem3271870 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271869 _85837 s t P x h1 h2) (@lem3271629 _85837 P x h1)). Qed.
Lemma lem3271871 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3271768 _85837 t x h1 h2) (fun h3 : False => @lem3271621 _85837 t x h2)). Qed.
Lemma lem3271872 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3271871 _85837 t x h1 h2) (@lem3271621 _85837 t x h2)). Qed.
Lemma lem3271873 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : (term40 _85837 t x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 t x => @lem3271872 _85837 t x h1 h2) (fun h3 : False => @lem3271619 _85837 t x h1)). Qed.
Lemma lem3271874 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3271873 _85837 t x h1 h2) (@lem3271619 _85837 t x h1)). Qed.
Lemma lem3271875 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271745 _85837 s t P x h1 h2) (fun h3 : False => @lem3271613 _85837 s x h1)). Qed.
Lemma lem3271876 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271875 _85837 s t P x h1 h2) (@lem3271613 _85837 s x h1)). Qed.
Lemma lem3271877 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271699 _85837 s t P x h1 h2) (fun h3 : False => @lem3271595 _85837 P x h1)). Qed.
Lemma lem3271878 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271877 _85837 s t P x h1 h2) (@lem3271595 _85837 P x h1)). Qed.
Lemma lem3271879 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271676 _85837 s t P x h1 h2) (fun h3 : False => @lem3271587 _85837 s x h1)). Qed.
Lemma lem3271880 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271879 _85837 s t P x h1 h2) (@lem3271587 _85837 s x h1)). Qed.
Lemma lem3271881 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271864 _85837 s t P x h1 h2) (fun h3 : False => @lem3271579 _85837 P x h1)). Qed.
Lemma lem3271882 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271881 _85837 s t P x h1 h2) (@lem3271579 _85837 P x h1)). Qed.
Lemma lem3271883 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271882 _85837 s t P x h1 h2) (fun h3 : False => @lem3271575 _85837 P x h1)). Qed.
Lemma lem3271884 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271883 _85837 s t P x h1 h2) (@lem3271575 _85837 P x h1)). Qed.
Lemma lem3271885 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271866 _85837 s t P x h1 h2) (fun h3 : False => @lem3271559 _85837 P x h1)). Qed.
Lemma lem3271886 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271885 _85837 s t P x h1 h2) (@lem3271559 _85837 P x h1)). Qed.
Lemma lem3271887 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271868 _85837 s t P x h1 h2) (fun h3 : False => @lem3271547 _85837 s x h1)). Qed.
Lemma lem3271888 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271887 _85837 s t P x h1 h2) (@lem3271547 _85837 s x h1)). Qed.
Lemma lem3271889 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271870 _85837 s t P x h1 h2) (fun h3 : False => @lem3271531 _85837 P x h1)). Qed.
Lemma lem3271890 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271889 _85837 s t P x h1 h2) (@lem3271531 _85837 P x h1)). Qed.
Lemma lem3271891 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3271874 _85837 t x h1 h2) (fun h3 : False => @lem3271515 _85837 t x h2)). Qed.
Lemma lem3271892 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3271891 _85837 t x h1 h2) (@lem3271515 _85837 t x h2)). Qed.
Lemma lem3271893 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : (term40 _85837 t x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 t x => @lem3271892 _85837 t x h1 h2) (fun h3 : False => @lem3271511 _85837 t x h1)). Qed.
Lemma lem3271894 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3271893 _85837 t x h1 h2) (@lem3271511 _85837 t x h1)). Qed.
Lemma lem3271895 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271876 _85837 s t P x h1 h2) (fun h3 : False => @lem3271499 _85837 s x h1)). Qed.
Lemma lem3271896 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271895 _85837 s t P x h1 h2) (@lem3271499 _85837 s x h1)). Qed.
Lemma lem3271897 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271878 _85837 s t P x h1 h2) (fun h3 : False => @lem3271463 _85837 P x h1)). Qed.
Lemma lem3271898 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271897 _85837 s t P x h1 h2) (@lem3271463 _85837 P x h1)). Qed.
Lemma lem3271899 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271880 _85837 s t P x h1 h2) (fun h3 : False => @lem3271447 _85837 s x h1)). Qed.
Lemma lem3271900 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271899 _85837 s t P x h1 h2) (@lem3271447 _85837 s x h1)). Qed.
Lemma lem3271901 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271884 _85837 s t P x h1 h2) (fun h3 : False => @lem3271579 _85837 P x h1)). Qed.
Lemma lem3271902 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271901 _85837 s t P x h1 h2) (@lem3271579 _85837 P x h1)). Qed.
Lemma lem3271903 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271902 _85837 s t P x h1 h2) (fun h3 : False => @lem3271575 _85837 P x h1)). Qed.
Lemma lem3271904 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271903 _85837 s t P x h1 h2) (@lem3271575 _85837 P x h1)). Qed.
Lemma lem3271905 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271886 _85837 s t P x h1 h2) (fun h3 : False => @lem3271559 _85837 P x h1)). Qed.
Lemma lem3271906 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271905 _85837 s t P x h1 h2) (@lem3271559 _85837 P x h1)). Qed.
Lemma lem3271907 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271888 _85837 s t P x h1 h2) (fun h3 : False => @lem3271547 _85837 s x h1)). Qed.
Lemma lem3271908 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271907 _85837 s t P x h1 h2) (@lem3271547 _85837 s x h1)). Qed.
Lemma lem3271909 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271890 _85837 s t P x h1 h2) (fun h3 : False => @lem3271531 _85837 P x h1)). Qed.
Lemma lem3271910 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271909 _85837 s t P x h1 h2) (@lem3271531 _85837 P x h1)). Qed.
Lemma lem3271911 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3271894 _85837 t x h1 h2) (fun h3 : False => @lem3271515 _85837 t x h2)). Qed.
Lemma lem3271912 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3271911 _85837 t x h1 h2) (@lem3271515 _85837 t x h2)). Qed.
Lemma lem3271913 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : (term40 _85837 t x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 t x => @lem3271912 _85837 t x h1 h2) (fun h3 : False => @lem3271511 _85837 t x h1)). Qed.
Lemma lem3271914 {_85837 : Type'} (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3271913 _85837 t x h1 h2) (@lem3271511 _85837 t x h1)). Qed.
Lemma lem3271915 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271896 _85837 s t P x h1 h2) (fun h3 : False => @lem3271499 _85837 s x h1)). Qed.
Lemma lem3271916 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271915 _85837 s t P x h1 h2) (@lem3271499 _85837 s x h1)). Qed.
Lemma lem3271917 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : (term40 _85837 P x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 P x => @lem3271898 _85837 s t P x h1 h2) (fun h3 : False => @lem3271463 _85837 P x h1)). Qed.
Lemma lem3271918 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271917 _85837 s t P x h1 h2) (@lem3271463 _85837 P x h1)). Qed.
Lemma lem3271919 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : (term40 _85837 s x) = False.
Proof. exact (prop_ext (fun h3 : term40 _85837 s x => @lem3271900 _85837 s t P x h1 h2) (fun h3 : False => @lem3271447 _85837 s x h1)). Qed.
Lemma lem3271920 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 s x) (h2 : term116 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271919 _85837 s t P x h1 h2) (@lem3271447 _85837 s x h1)). Qed.
Lemma lem3271921 {_85837 : Type'} (P : _85837 -> Prop) (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) (h3 : term95 _85837 s t x) : False.
Proof. exact (or_elim (@lem3271428 _85837 s t x h3) (fun h0 : term40 _85837 s x => @lem3271908 _85837 s t P x h0 h2) (fun h0 : t x => @lem3271906 _85837 s t P x h1 h2)). Qed.
Lemma lem3271922 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 P x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (or_elim (@lem3271417 _85837 s t P x h2) (fun h0 : term95 _85837 s t x => @lem3271921 _85837 P s t x h1 h2 h0) (fun h0 : term40 _85837 P x => @lem3271904 _85837 s t P x h1 h2)). Qed.
Lemma lem3271923 {_85837 : Type'} (P : _85837 -> Prop) (s : _85837 -> Prop) (t : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : term113 _85837 s t P x) (h3 : term95 _85837 s t x) : False.
Proof. exact (or_elim (@lem3271424 _85837 s t x h3) (fun h0 : term40 _85837 s x => @lem3271916 _85837 s t P x h0 h2) (fun h0 : t x => @lem3271914 _85837 t x h1 h0)). Qed.
Lemma lem3271924 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term40 _85837 t x) (h2 : term113 _85837 s t P x) : False.
Proof. exact (or_elim (@lem3271417 _85837 s t P x h2) (fun h0 : term95 _85837 s t x => @lem3271923 _85837 P s t x h1 h2 h0) (fun h0 : term40 _85837 P x => @lem3271910 _85837 s t P x h0 h2)). Qed.
Lemma lem3271925 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term113 _85837 s t P x) : False.
Proof. exact (or_elim (@lem3271418 _85837 s t P x h1) (fun h0 : term40 _85837 t x => @lem3271924 _85837 s t P x h0 h1) (fun h0 : term40 _85837 P x => @lem3271922 _85837 s t P x h0 h1)). Qed.
Lemma lem3271926 {_85837 : Type'} (t : _85837 -> Prop) (s : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) (h2 : term102 _85837 s P x) : False.
Proof. exact (or_elim (@lem3271410 _85837 s P x h2) (fun h0 : term40 _85837 s x => @lem3271920 _85837 s t P x h0 h1) (fun h0 : term40 _85837 P x => @lem3271918 _85837 s t P x h0 h1)). Qed.
Lemma lem3271927 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term116 _85837 s t P x) : False.
Proof. exact (or_elim (@lem3271404 _85837 s t P x h1) (fun h0 : term102 _85837 s P x => @lem3271926 _85837 t s P x h1 h0) (fun h0 : term67 _85837 t P x => @lem3271722 _85837 s t P x h0 h1)). Qed.
Lemma lem3271928 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term91 _85837 s t P x) : False.
Proof. exact (or_elim (@lem3271401 _85837 s t P x h1) (fun h0 : term116 _85837 s t P x => @lem3271927 _85837 s t P x h0) (fun h0 : term113 _85837 s t P x => @lem3271925 _85837 s t P x h0)). Qed.
Lemma lem3271929 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term91 _85837 s t P x) : (term91 _85837 s t P x) = False.
Proof. exact (prop_ext (fun h2 : term91 _85837 s t P x => @lem3271928 _85837 s t P x h1) (fun h2 : False => @lem3271231 _85837 s t P x h1)). Qed.
Lemma lem3271930 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) (h1 : term91 _85837 s t P x) : False.
Proof. exact (EQ_MP (@lem3271929 _85837 s t P x h1) (@lem3271231 _85837 s t P x h1)). Qed.
Lemma lem3271931 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : term90 _85837 s t P x.
Proof. exact (fun h0 : term91 _85837 s t P x => @lem3271930 _85837 s t P x h0). Qed.
Lemma lem3271932 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) (x : _85837) : (term44 _85837 s t P x) = (term72 _85837 s t P x).
Proof. exact (EQ_MP (@lem3271230 _85837 s t P x) (@lem3271931 _85837 s t P x)). Qed.
Lemma lem3271937 {_85837 : Type'} (s : _85837 -> Prop) (t : _85837 -> Prop) (P : _85837 -> Prop) : term75 _85837 s t P.
Proof. exact (fun x : _85837 => @lem3271932 _85837 s t P x). Qed.
Lemma lem3271942 {_85837 : Type'} (s : _85837 -> Prop) (P : _85837 -> Prop) : term77 _85837 s P.
Proof. exact (fun t : _85837 -> Prop => @lem3271937 _85837 s t P). Qed.
Lemma lem3271947 {_85837 : Type'} (P : _85837 -> Prop) : term79 _85837 P.
Proof. exact (fun s : _85837 -> Prop => @lem3271942 _85837 s P). Qed.
Lemma lem3271952 {_85837 : Type'} : term81 _85837.
Proof. exact (fun P : _85837 -> Prop => @lem3271947 _85837 P). Qed.
Lemma lem3271953 {_85837 : Type'} : term83 _85837.
Proof. exact (EQ_MP (@lem3271226 _85837) (@lem3271952 _85837)). Qed.
Lemma lem3271955 {_85837 : Type'} : term83 _85837.
Proof. exact (@lem3271110 _85837 (@lem3271953 _85837)). Qed.
Lemma lem3271956 {_85837 : Type'} (h1 : term84 _85837) : False.
Proof. exact (@lem3271955 _85837 (@lem3271094 _85837 h1)). Qed.
Lemma lem3271957 {_85837 : Type'} (h1 : term84 _85837) : (term84 _85837) = False.
Proof. exact (prop_ext (fun h2 : term84 _85837 => @lem3271956 _85837 h1) (fun h2 : False => @lem3271094 _85837 h1)). Qed.
Lemma lem3271958 {_85837 : Type'} (h1 : term84 _85837) : False.
Proof. exact (EQ_MP (@lem3271957 _85837 h1) (@lem3271094 _85837 h1)). Qed.
Lemma lem3271959 {_85837 : Type'} : term83 _85837.
Proof. exact (fun h0 : term84 _85837 => @lem3271958 _85837 h0). Qed.
Lemma lem3271960 {_85837 : Type'} : term81 _85837.
Proof. exact (EQ_MP (@lem3271093 _85837) (@lem3271959 _85837)). Qed.
Lemma lem3271961 {_85837 : Type'} : term15 _85837.
Proof. exact (EQ_MP (@lem3271089 _85837) (@lem3271960 _85837)). Qed.
Lemma lem3271962 {_85837 : Type'} : term14 _85837.
Proof. exact (EQ_MP (@lem3270901 _85837) (@lem3271961 _85837)). Qed.
