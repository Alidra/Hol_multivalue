Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_IMAGE_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3397820 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3397821 {_88266 : Type'} (s : _88266 -> Prop) (t : _88266 -> Prop) : (s = t) = (term0 _88266 s t).
Proof. exact (@lem3397820 _88266 s t). Qed.
Lemma lem3397822 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : ((@IMAGE _88270 _88266 f s) = t) = (term1 _88266 _88270 f s t).
Proof. exact (@lem3397821 _88266 (@IMAGE _88270 _88266 f s) t). Qed.
Lemma lem3397831 {_88266 _88270 : Type'} (f : _88270 -> _88266) (t : _88266 -> Prop) (s : _88270 -> Prop) : (term2 _88266 _88270 f t s) = (term2 _88266 _88270 f t s).
Proof. exact (eq_refl (term2 _88266 _88270 f t s)). Qed.
Lemma lem3397832 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term3 _88266 _88270 f s t) = (term4 _88266 _88270 f s t).
Proof. exact (MK_COMB (@lem3397831 _88266 _88270 f t s) (@lem3397822 _88266 _88270 f s t)). Qed.
Lemma lem3397835 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term5 _88266 _88270 f s) = (term6 _88266 _88270 f s).
Proof. exact (fun_ext (fun t : _88266 -> Prop => @lem3397832 _88266 _88270 f s t)). Qed.
Lemma lem3397836 {_88266 : Type'} : (@all (_88266 -> Prop)) = (@all (_88266 -> Prop)).
Proof. exact (eq_refl (@all (_88266 -> Prop))). Qed.
Lemma lem3397837 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term7 _88266 _88270 f s) = (term8 _88266 _88270 f s).
Proof. exact (MK_COMB (@lem3397836 _88266) (@lem3397835 _88266 _88270 f s)). Qed.
Lemma lem3397842 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term9 _88266 _88270 f) = (term10 _88266 _88270 f).
Proof. exact (fun_ext (fun s : _88270 -> Prop => @lem3397837 _88266 _88270 f s)). Qed.
Lemma lem3397843 {_88270 : Type'} : (@all (_88270 -> Prop)) = (@all (_88270 -> Prop)).
Proof. exact (eq_refl (@all (_88270 -> Prop))). Qed.
Lemma lem3397844 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term11 _88266 _88270 f) = (term12 _88266 _88270 f).
Proof. exact (MK_COMB (@lem3397843 _88270) (@lem3397842 _88266 _88270 f)). Qed.
Lemma lem3397849 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term12 _88266 _88270 f) = (term11 _88266 _88270 f).
Proof. exact (SYM (@lem3397844 _88266 _88270 f)). Qed.
Lemma lem3397869 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3397870 {_88266 : Type'} (P : _88266 -> Prop) (x : _88266) : (@IN _88266 x P) = (P x).
Proof. exact (@lem3397869 _88266 P x). Qed.
Lemma lem3397871 {_88266 : Type'} (t : _88266 -> Prop) (y : _88266) : (@IN _88266 y t) = (t y).
Proof. exact (@lem3397870 _88266 t y). Qed.
Lemma lem3397872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3397873 {_88266 : Type'} (t : _88266 -> Prop) (y : _88266) : (term13 _88266 y t) = (term14 _88266 t y).
Proof. exact (MK_COMB (@lem3397872) (@lem3397871 _88266 t y)). Qed.
Lemma lem3397880 {_88266 _88270 : Type'} (f : _88270 -> _88266) (y : _88266) : (term15 _88266 _88270 f y) = (term15 _88266 _88270 f y).
Proof. exact (eq_refl (term15 _88266 _88270 f y)). Qed.
Lemma lem3397881 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term16 _88266 _88270 t f y) = (term17 _88266 _88270 t f y).
Proof. exact (MK_COMB (@lem3397873 _88266 t y) (@lem3397880 _88266 _88270 f y)). Qed.
Lemma lem3397884 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term18 _88266 _88270 t f) = (term19 _88266 _88270 t f).
Proof. exact (fun_ext (fun y : _88266 => @lem3397881 _88266 _88270 t f y)). Qed.
Lemma lem3397885 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3397886 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term20 _88266 _88270 t f) = (term21 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3397885 _88266) (@lem3397884 _88266 _88270 t f)). Qed.
Lemma lem3397891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3397892 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term22 _88266 _88270 t f) = (term23 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3397891) (@lem3397886 _88266 _88270 t f)). Qed.
Lemma lem3397900 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3397901 {_88266 : Type'} (P : _88266 -> Prop) (x : _88266) : (@IN _88266 x P) = (P x).
Proof. exact (@lem3397900 _88266 P x). Qed.
Lemma lem3397902 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88270) : (term24 _88266 _88270 f x t) = (term25 _88266 _88270 t f x).
Proof. exact (@lem3397901 _88266 t (f x)). Qed.
Lemma lem3397903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3397904 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88270) : (term26 _88266 _88270 f x t) = (term27 _88266 _88270 t f x).
Proof. exact (MK_COMB (@lem3397903) (@lem3397902 _88266 _88270 t f x)). Qed.
Lemma lem3397906 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3397907 {_88270 : Type'} (P : _88270 -> Prop) (x : _88270) : (@IN _88270 x P) = (P x).
Proof. exact (@lem3397906 _88270 P x). Qed.
Lemma lem3397908 {_88270 : Type'} (s : _88270 -> Prop) (x : _88270) : (@IN _88270 x s) = (s x).
Proof. exact (@lem3397907 _88270 s x). Qed.
Lemma lem3397909 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : ((term24 _88266 _88270 f x t) = (@IN _88270 x s)) = ((term25 _88266 _88270 t f x) = (s x)).
Proof. exact (MK_COMB (@lem3397904 _88266 _88270 t f x) (@lem3397908 _88270 s x)). Qed.
Lemma lem3397912 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term28 _88266 _88270 f t s) = (term29 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3397909 _88266 _88270 t f s x)). Qed.
Lemma lem3397913 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3397914 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term30 _88266 _88270 f t s) = (term31 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3397913 _88270) (@lem3397912 _88266 _88270 t f s)). Qed.
Lemma lem3397919 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term32 _88266 _88270 f t s) = (term33 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3397892 _88266 _88270 t f) (@lem3397914 _88266 _88270 t f s)). Qed.
Lemma lem3397922 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3397923 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term2 _88266 _88270 f t s) = (term34 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3397922) (@lem3397919 _88266 _88270 t f s)). Qed.
Lemma lem3397931 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term35 A B y f s) = (term36 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3397932 {_88266 _88270 : Type'} (y : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term37 _88266 _88270 y f s) = (term38 _88266 _88270 y f s).
Proof. exact (@lem3397931 _88270 _88266 y f s). Qed.
Lemma lem3397933 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term37 _88266 _88270 x f s) = (term38 _88266 _88270 x f s).
Proof. exact (@lem3397932 _88266 _88270 x f s). Qed.
Lemma lem3397943 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3397944 {_88270 : Type'} (P : _88270 -> Prop) (x : _88270) : (@IN _88270 x P) = (P x).
Proof. exact (@lem3397943 _88270 P x). Qed.
Lemma lem3397945 {_88270 : Type'} (s : _88270 -> Prop) (x : _88270) : (@IN _88270 x s) = (s x).
Proof. exact (@lem3397944 _88270 s x). Qed.
Lemma lem3397946 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (x' : _88270) : (term39 _88266 _88270 x f x') = (term39 _88266 _88270 x f x').
Proof. exact (eq_refl (term39 _88266 _88270 x f x')). Qed.
Lemma lem3397947 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term40 _88266 _88270 x f x' s) = (term41 _88266 _88270 x f s x').
Proof. exact (MK_COMB (@lem3397946 _88266 _88270 x f x') (@lem3397945 _88270 s x')). Qed.
Lemma lem3397950 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term42 _88266 _88270 x f s) = (term43 _88266 _88270 x f s).
Proof. exact (fun_ext (fun x' : _88270 => @lem3397947 _88266 _88270 x f s x')). Qed.
Lemma lem3397951 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3397952 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term38 _88266 _88270 x f s) = (term44 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3397951 _88270) (@lem3397950 _88266 _88270 x f s)). Qed.
Lemma lem3397957 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term37 _88266 _88270 x f s) = (term44 _88266 _88270 x f s).
Proof. exact (TRANS (@lem3397933 _88266 _88270 x f s) (@lem3397952 _88266 _88270 x f s)). Qed.
Lemma lem3397958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3397959 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term45 _88266 _88270 x f s) = (term46 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3397958) (@lem3397957 _88266 _88270 x f s)). Qed.
Lemma lem3397961 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3397962 {_88266 : Type'} (P : _88266 -> Prop) (x : _88266) : (@IN _88266 x P) = (P x).
Proof. exact (@lem3397961 _88266 P x). Qed.
Lemma lem3397963 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (@IN _88266 x t) = (t x).
Proof. exact (@lem3397962 _88266 t x). Qed.
Lemma lem3397964 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : ((term37 _88266 _88270 x f s) = (@IN _88266 x t)) = ((term44 _88266 _88270 x f s) = (t x)).
Proof. exact (MK_COMB (@lem3397959 _88266 _88270 x f s) (@lem3397963 _88266 t x)). Qed.
Lemma lem3397967 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term47 _88266 _88270 f s t) = (term48 _88266 _88270 f s t).
Proof. exact (fun_ext (fun x : _88266 => @lem3397964 _88266 _88270 f s t x)). Qed.
Lemma lem3397968 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3397969 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term1 _88266 _88270 f s t) = (term49 _88266 _88270 f s t).
Proof. exact (MK_COMB (@lem3397968 _88266) (@lem3397967 _88266 _88270 f s t)). Qed.
Lemma lem3397974 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term4 _88266 _88270 f s t) = (term50 _88266 _88270 f s t).
Proof. exact (MK_COMB (@lem3397923 _88266 _88270 t f s) (@lem3397969 _88266 _88270 f s t)). Qed.
Lemma lem3397977 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term6 _88266 _88270 f s) = (term51 _88266 _88270 f s).
Proof. exact (fun_ext (fun t : _88266 -> Prop => @lem3397974 _88266 _88270 f s t)). Qed.
Lemma lem3397978 {_88266 : Type'} : (@all (_88266 -> Prop)) = (@all (_88266 -> Prop)).
Proof. exact (eq_refl (@all (_88266 -> Prop))). Qed.
Lemma lem3397979 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term8 _88266 _88270 f s) = (term52 _88266 _88270 f s).
Proof. exact (MK_COMB (@lem3397978 _88266) (@lem3397977 _88266 _88270 f s)). Qed.
Lemma lem3397984 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term10 _88266 _88270 f) = (term53 _88266 _88270 f).
Proof. exact (fun_ext (fun s : _88270 -> Prop => @lem3397979 _88266 _88270 f s)). Qed.
Lemma lem3397985 {_88270 : Type'} : (@all (_88270 -> Prop)) = (@all (_88270 -> Prop)).
Proof. exact (eq_refl (@all (_88270 -> Prop))). Qed.
Lemma lem3397986 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term12 _88266 _88270 f) = (term54 _88266 _88270 f).
Proof. exact (MK_COMB (@lem3397985 _88270) (@lem3397984 _88266 _88270 f)). Qed.
Lemma lem3397991 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term54 _88266 _88270 f) = (term12 _88266 _88270 f).
Proof. exact (SYM (@lem3397986 _88266 _88270 f)). Qed.
Lemma lem3397993 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3397994 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term54 _88266 _88270 f) = (term56 _88266 _88270 f).
Proof. exact (@lem3397993 (term54 _88266 _88270 f)). Qed.
Lemma lem3397995 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term56 _88266 _88270 f) = (term54 _88266 _88270 f).
Proof. exact (SYM (@lem3397994 _88266 _88270 f)). Qed.
Lemma lem3397996 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term57 _88266 _88270 f) : term57 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem3397999 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term56 _88266 _88270 f) : term56 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem3398000 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term58 _88266 _88270 f.
Proof. exact (fun h0 : term56 _88266 _88270 f => @lem3397999 _88266 _88270 f h0). Qed.
Lemma lem3398001 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term58 _88266 _88270 f) : term58 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem3398002 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term56 _88266 _88270 f) : term56 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem3398003 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term56 _88266 _88270 f) (h2 : term58 _88266 _88270 f) : term56 _88266 _88270 f.
Proof. exact (@lem3398001 _88266 _88270 f h2 (@lem3398002 _88266 _88270 f h1)). Qed.
Lemma lem3398004 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term56 _88266 _88270 f) : term59 _88266 _88270 f.
Proof. exact (fun h0 : term58 _88266 _88270 f => @lem3398003 _88266 _88270 f h1 h0). Qed.
Lemma lem3398005 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term58 _88266 _88270 f) : term58 _88266 _88270 f.
Proof. exact (h1). Qed.
Lemma lem3398006 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term56 _88266 _88270 f) (h2 : term58 _88266 _88270 f) : term56 _88266 _88270 f.
Proof. exact (@lem3398004 _88266 _88270 f h1 (@lem3398005 _88266 _88270 f h2)). Qed.
Lemma lem3398007 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term58 _88266 _88270 f) : term58 _88266 _88270 f.
Proof. exact (fun h0 : term56 _88266 _88270 f => @lem3398006 _88266 _88270 f h0 h1). Qed.
Lemma lem3398008 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term60 _88266 _88270 f.
Proof. exact (fun h0 : term58 _88266 _88270 f => @lem3398007 _88266 _88270 f h0). Qed.
Lemma lem3398011 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term58 _88266 _88270 f.
Proof. exact (@lem3398008 _88266 _88270 f (@lem3398000 _88266 _88270 f)). Qed.
Lemma lem3398012 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term58 _88266 _88270 f.
Proof. exact (@lem3398011 _88266 _88270 f). Qed.
Lemma lem3398018 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3398019 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term56 _88266 _88270 f) = (term61 _88266 _88270 f).
Proof. exact (@lem3398018 (term57 _88266 _88270 f)). Qed.
Lemma lem3398021 (t : Prop) : (term62 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3398022 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term61 _88266 _88270 f) = (term54 _88266 _88270 f).
Proof. exact (@lem3398021 (term54 _88266 _88270 f)). Qed.
Lemma lem3398027 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term56 _88266 _88270 f) = (term54 _88266 _88270 f).
Proof. exact (TRANS (@lem3398019 _88266 _88270 f) (@lem3398022 _88266 _88270 f)). Qed.
Lemma lem3398088 {_88266 _88270 : Type'} : (term63 _88266 _88270) = (term64 _88266 _88270).
Proof. exact (fun_ext (fun f : _88270 -> _88266 => @lem3398027 _88266 _88270 f)). Qed.
Lemma lem3398089 {_88266 _88270 : Type'} : (@all (_88270 -> _88266)) = (@all (_88270 -> _88266)).
Proof. exact (eq_refl (@all (_88270 -> _88266))). Qed.
Lemma lem3398098 {_88266 _88270 : Type'} : (term65 _88266 _88270) = (term66 _88266 _88270).
Proof. exact (MK_COMB (@lem3398089 _88266 _88270) (@lem3398088 _88266 _88270)). Qed.
Lemma lem3398099 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3398104 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term41 _88266 _88270 x f s x') = (term41 _88266 _88270 x f s x').
Proof. exact (eq_refl (term41 _88266 _88270 x f s x')). Qed.
Lemma lem3398105 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term43 _88266 _88270 x f s) = (term43 _88266 _88270 x f s).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398104 _88266 _88270 x f s x')). Qed.
Lemma lem3398106 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398107 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term44 _88266 _88270 x f s) = (term44 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398106 _88270) (@lem3398105 _88266 _88270 x f s)). Qed.
Lemma lem3398108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3398109 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term46 _88266 _88270 x f s) = (term46 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398108) (@lem3398107 _88266 _88270 x f s)). Qed.
Lemma lem3398110 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : ((term44 _88266 _88270 x f s) = (t x)) = ((term44 _88266 _88270 x f s) = (t x)).
Proof. exact (MK_COMB (@lem3398109 _88266 _88270 x f s) (@lem3398099 _88266 t x)). Qed.
Lemma lem3398111 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term48 _88266 _88270 f s t) = (term48 _88266 _88270 f s t).
Proof. exact (fun_ext (fun x : _88266 => @lem3398110 _88266 _88270 f s t x)). Qed.
Lemma lem3398112 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398113 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term49 _88266 _88270 f s t) = (term49 _88266 _88270 f s t).
Proof. exact (MK_COMB (@lem3398112 _88266) (@lem3398111 _88266 _88270 f s t)). Qed.
Lemma lem3398118 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : ((term25 _88266 _88270 t f x) = (s x)) = ((term25 _88266 _88270 t f x) = (s x)).
Proof. exact (eq_refl ((term25 _88266 _88270 t f x) = (s x))). Qed.
Lemma lem3398119 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term29 _88266 _88270 t f s) = (term29 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398118 _88266 _88270 t f s x)). Qed.
Lemma lem3398120 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398121 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term31 _88266 _88270 t f s) = (term31 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398120 _88270) (@lem3398119 _88266 _88270 t f s)). Qed.
Lemma lem3398122 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x : _88270) (y : _88266) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3398123 {_88266 _88270 : Type'} (f : _88270 -> _88266) (y : _88266) : (term67 _88266 _88270 f y) = (term67 _88266 _88270 f y).
Proof. exact (fun_ext (fun x : _88270 => @lem3398122 _88266 _88270 f x y)). Qed.
Lemma lem3398124 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398125 {_88266 _88270 : Type'} (f : _88270 -> _88266) (y : _88266) : (term15 _88266 _88270 f y) = (term15 _88266 _88270 f y).
Proof. exact (MK_COMB (@lem3398124 _88270) (@lem3398123 _88266 _88270 f y)). Qed.
Lemma lem3398128 {_88266 : Type'} (t : _88266 -> Prop) (y : _88266) : (term14 _88266 t y) = (term14 _88266 t y).
Proof. exact (eq_refl (term14 _88266 t y)). Qed.
Lemma lem3398129 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term17 _88266 _88270 t f y) = (term17 _88266 _88270 t f y).
Proof. exact (MK_COMB (@lem3398128 _88266 t y) (@lem3398125 _88266 _88270 f y)). Qed.
Lemma lem3398130 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term19 _88266 _88270 t f) = (term19 _88266 _88270 t f).
Proof. exact (fun_ext (fun y : _88266 => @lem3398129 _88266 _88270 t f y)). Qed.
Lemma lem3398131 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398132 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term21 _88266 _88270 t f) = (term21 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398131 _88266) (@lem3398130 _88266 _88270 t f)). Qed.
Lemma lem3398133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398134 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term23 _88266 _88270 t f) = (term23 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398133) (@lem3398132 _88266 _88270 t f)). Qed.
Lemma lem3398135 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term33 _88266 _88270 t f s) = (term33 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398134 _88266 _88270 t f) (@lem3398121 _88266 _88270 t f s)). Qed.
Lemma lem3398136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3398137 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term34 _88266 _88270 t f s) = (term34 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398136) (@lem3398135 _88266 _88270 t f s)). Qed.
Lemma lem3398138 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : (term50 _88266 _88270 f s t) = (term50 _88266 _88270 f s t).
Proof. exact (MK_COMB (@lem3398137 _88266 _88270 t f s) (@lem3398113 _88266 _88270 f s t)). Qed.
Lemma lem3398139 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term51 _88266 _88270 f s) = (term51 _88266 _88270 f s).
Proof. exact (fun_ext (fun t : _88266 -> Prop => @lem3398138 _88266 _88270 f s t)). Qed.
Lemma lem3398140 {_88266 : Type'} : (@all (_88266 -> Prop)) = (@all (_88266 -> Prop)).
Proof. exact (eq_refl (@all (_88266 -> Prop))). Qed.
Lemma lem3398141 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : (term52 _88266 _88270 f s) = (term52 _88266 _88270 f s).
Proof. exact (MK_COMB (@lem3398140 _88266) (@lem3398139 _88266 _88270 f s)). Qed.
Lemma lem3398142 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term53 _88266 _88270 f) = (term53 _88266 _88270 f).
Proof. exact (fun_ext (fun s : _88270 -> Prop => @lem3398141 _88266 _88270 f s)). Qed.
Lemma lem3398143 {_88270 : Type'} : (@all (_88270 -> Prop)) = (@all (_88270 -> Prop)).
Proof. exact (eq_refl (@all (_88270 -> Prop))). Qed.
Lemma lem3398144 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term54 _88266 _88270 f) = (term54 _88266 _88270 f).
Proof. exact (MK_COMB (@lem3398143 _88270) (@lem3398142 _88266 _88270 f)). Qed.
Lemma lem3398145 {_88266 _88270 : Type'} : (term64 _88266 _88270) = (term64 _88266 _88270).
Proof. exact (fun_ext (fun f : _88270 -> _88266 => @lem3398144 _88266 _88270 f)). Qed.
Lemma lem3398146 {_88266 _88270 : Type'} : (@all (_88270 -> _88266)) = (@all (_88270 -> _88266)).
Proof. exact (eq_refl (@all (_88270 -> _88266))). Qed.
Lemma lem3398147 {_88266 _88270 : Type'} : (term66 _88266 _88270) = (term66 _88266 _88270).
Proof. exact (MK_COMB (@lem3398146 _88266 _88270) (@lem3398145 _88266 _88270)). Qed.
Lemma lem3398206 {_88266 _88270 : Type'} : (term65 _88266 _88270) = (term66 _88266 _88270).
Proof. exact (TRANS (@lem3398098 _88266 _88270) (@lem3398147 _88266 _88270)). Qed.
Lemma lem3398207 {_88266 _88270 : Type'} : (term66 _88266 _88270) = (term65 _88266 _88270).
Proof. exact (SYM (@lem3398206 _88266 _88270)). Qed.
Lemma lem3398208 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term33 _88266 _88270 t f s) : term33 _88266 _88270 t f s.
Proof. exact (h1). Qed.
Lemma lem3398210 (p : Prop) : p = (term55 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3398211 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : ((term44 _88266 _88270 x f s) = (t x)) = (term68 _88266 _88270 f s t x).
Proof. exact (@lem3398210 ((term44 _88266 _88270 x f s) = (t x))). Qed.
Lemma lem3398212 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term68 _88266 _88270 f s t x) = ((term44 _88266 _88270 x f s) = (t x)).
Proof. exact (SYM (@lem3398211 _88266 _88270 f s t x)). Qed.
Lemma lem3398213 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term69 _88266 _88270 f s t x) : term69 _88266 _88270 f s t x.
Proof. exact (h1). Qed.
Lemma lem3398215 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x : _88270) (y : _88266) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3398216 {_88266 _88270 : Type'} (f : _88270 -> _88266) (y : _88266) : (term67 _88266 _88270 f y) = (term67 _88266 _88270 f y).
Proof. exact (fun_ext (fun x : _88270 => @lem3398215 _88266 _88270 f x y)). Qed.
Lemma lem3398217 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398218 {_88266 _88270 : Type'} (f : _88270 -> _88266) (y : _88266) : (term15 _88266 _88270 f y) = (term15 _88266 _88270 f y).
Proof. exact (MK_COMB (@lem3398217 _88270) (@lem3398216 _88266 _88270 f y)). Qed.
Lemma lem3398220 {_88266 : Type'} (t : _88266 -> Prop) (y : _88266) : (term70 _88266 t y) = (term70 _88266 t y).
Proof. exact (eq_refl (term70 _88266 t y)). Qed.
Lemma lem3398221 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term71 _88266 _88270 t f y) = (term71 _88266 _88270 t f y).
Proof. exact (MK_COMB (@lem3398220 _88266 t y) (@lem3398218 _88266 _88270 f y)). Qed.
Lemma lem3398222 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term17 _88266 _88270 t f y) = (term71 _88266 _88270 t f y).
Proof. exact (@lem17265 (t y) (term15 _88266 _88270 f y)). Qed.
Lemma lem3398223 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term17 _88266 _88270 t f y) = (term71 _88266 _88270 t f y).
Proof. exact (TRANS (@lem3398222 _88266 _88270 t f y) (@lem3398221 _88266 _88270 t f y)). Qed.
Lemma lem3398224 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term19 _88266 _88270 t f) = (term72 _88266 _88270 t f).
Proof. exact (fun_ext (fun y : _88266 => @lem3398223 _88266 _88270 t f y)). Qed.
Lemma lem3398225 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398226 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term21 _88266 _88270 t f) = (term73 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398225 _88266) (@lem3398224 _88266 _88270 t f)). Qed.
Lemma lem3398241 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : ((term25 _88266 _88270 t f x) = (s x)) = (term74 _88266 _88270 t f s x).
Proof. exact (@lem17784 (term25 _88266 _88270 t f x) (s x)). Qed.
Lemma lem3398242 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term29 _88266 _88270 t f s) = (term75 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398241 _88266 _88270 t f s x)). Qed.
Lemma lem3398243 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398244 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term31 _88266 _88270 t f s) = (term76 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398243 _88270) (@lem3398242 _88266 _88270 t f s)). Qed.
Lemma lem3398245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398246 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term23 _88266 _88270 t f) = (term77 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398245) (@lem3398226 _88266 _88270 t f)). Qed.
Lemma lem3398247 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term33 _88266 _88270 t f s) = (term78 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398246 _88266 _88270 t f) (@lem3398244 _88266 _88270 t f s)). Qed.
Lemma lem3398301 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3398302 {_88270 : Type'} (P : _88270 -> Prop) (Q : _88270 -> Prop) : (term79 _88270 P Q) = (term80 _88270 P Q).
Proof. exact (@lem3398301 _88270 P Q). Qed.
Lemma lem3398303 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term81 _88266 _88270 t f s) = (term82 _88266 _88270 t f s).
Proof. exact (@lem3398302 _88270 (term83 _88266 _88270 t f s) (term84 _88266 _88270 t f s)). Qed.
Lemma lem3398304 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term85 _88266 _88270 t f s x) = (term86 _88266 _88270 t f s x).
Proof. exact (eq_refl (term85 _88266 _88270 t f s x)). Qed.
Lemma lem3398305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398306 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term87 _88266 _88270 t f s x) = (term88 _88266 _88270 t f s x).
Proof. exact (MK_COMB (@lem3398305) (@lem3398304 _88266 _88270 t f s x)). Qed.
Lemma lem3398307 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term89 _88266 _88270 t f s x) = (term90 _88266 _88270 t f s x).
Proof. exact (eq_refl (term89 _88266 _88270 t f s x)). Qed.
Lemma lem3398308 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term91 _88266 _88270 t f s x) = (term74 _88266 _88270 t f s x).
Proof. exact (MK_COMB (@lem3398306 _88266 _88270 t f s x) (@lem3398307 _88266 _88270 t f s x)). Qed.
Lemma lem3398309 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term92 _88266 _88270 t f s) = (term75 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398308 _88266 _88270 t f s x)). Qed.
Lemma lem3398310 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398311 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term81 _88266 _88270 t f s) = (term76 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398310 _88270) (@lem3398309 _88266 _88270 t f s)). Qed.
Lemma lem3398312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3398313 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term93 _88266 _88270 t f s) = (term94 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398312) (@lem3398311 _88266 _88270 t f s)). Qed.
Lemma lem3398314 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term85 _88266 _88270 t f s x) = (term86 _88266 _88270 t f s x).
Proof. exact (eq_refl (term85 _88266 _88270 t f s x)). Qed.
Lemma lem3398315 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term95 _88266 _88270 t f s) = (term83 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398314 _88266 _88270 t f s x)). Qed.
Lemma lem3398316 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398317 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term96 _88266 _88270 t f s) = (term97 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398316 _88270) (@lem3398315 _88266 _88270 t f s)). Qed.
Lemma lem3398318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398319 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term98 _88266 _88270 t f s) = (term99 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398318) (@lem3398317 _88266 _88270 t f s)). Qed.
Lemma lem3398320 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term89 _88266 _88270 t f s x) = (term90 _88266 _88270 t f s x).
Proof. exact (eq_refl (term89 _88266 _88270 t f s x)). Qed.
Lemma lem3398321 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term100 _88266 _88270 t f s) = (term84 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398320 _88266 _88270 t f s x)). Qed.
Lemma lem3398322 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398323 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term101 _88266 _88270 t f s) = (term102 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398322 _88270) (@lem3398321 _88266 _88270 t f s)). Qed.
Lemma lem3398324 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term82 _88266 _88270 t f s) = (term103 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398319 _88266 _88270 t f s) (@lem3398323 _88266 _88270 t f s)). Qed.
Lemma lem3398325 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : ((term81 _88266 _88270 t f s) = (term82 _88266 _88270 t f s)) = ((term76 _88266 _88270 t f s) = (term103 _88266 _88270 t f s)).
Proof. exact (MK_COMB (@lem3398313 _88266 _88270 t f s) (@lem3398324 _88266 _88270 t f s)). Qed.
Lemma lem3398326 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term76 _88266 _88270 t f s) = (term103 _88266 _88270 t f s).
Proof. exact (EQ_MP (@lem3398325 _88266 _88270 t f s) (@lem3398303 _88266 _88270 t f s)). Qed.
Lemma lem3398407 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term77 _88266 _88270 t f) = (term77 _88266 _88270 t f).
Proof. exact (eq_refl (term77 _88266 _88270 t f)). Qed.
Lemma lem3398408 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term78 _88266 _88270 t f s) = (term104 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398407 _88266 _88270 t f) (@lem3398326 _88266 _88270 t f s)). Qed.
Lemma lem3398410 {A : Type'} (P : Prop) (Q : A -> Prop) : (term105 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3398411 {_88270 : Type'} (P : Prop) (Q : _88270 -> Prop) : (term105 _88270 P Q) = (term106 _88270 P Q).
Proof. exact (@lem3398410 _88270 P Q). Qed.
Lemma lem3398412 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term107 _88266 _88270 t f y) = (term108 _88266 _88270 t f y).
Proof. exact (@lem3398411 _88270 (term109 _88266 t y) (term67 _88266 _88270 f y)). Qed.
Lemma lem3398413 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x : _88270) (y : _88266) : (term110 _88266 _88270 f y x) = ((f x) = y).
Proof. exact (eq_refl (term110 _88266 _88270 f y x)). Qed.
Lemma lem3398414 {_88266 _88270 : Type'} (f : _88270 -> _88266) (y : _88266) : (term111 _88266 _88270 f y) = (term67 _88266 _88270 f y).
Proof. exact (fun_ext (fun x : _88270 => @lem3398413 _88266 _88270 f x y)). Qed.
Lemma lem3398415 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398416 {_88266 _88270 : Type'} (f : _88270 -> _88266) (y : _88266) : (term112 _88266 _88270 f y) = (term15 _88266 _88270 f y).
Proof. exact (MK_COMB (@lem3398415 _88270) (@lem3398414 _88266 _88270 f y)). Qed.
Lemma lem3398417 {_88266 : Type'} (t : _88266 -> Prop) (y : _88266) : (term70 _88266 t y) = (term70 _88266 t y).
Proof. exact (eq_refl (term70 _88266 t y)). Qed.
Lemma lem3398418 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term107 _88266 _88270 t f y) = (term71 _88266 _88270 t f y).
Proof. exact (MK_COMB (@lem3398417 _88266 t y) (@lem3398416 _88266 _88270 f y)). Qed.
Lemma lem3398419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3398420 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term113 _88266 _88270 t f y) = (term114 _88266 _88270 t f y).
Proof. exact (MK_COMB (@lem3398419) (@lem3398418 _88266 _88270 t f y)). Qed.
Lemma lem3398421 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x : _88270) (y : _88266) : (term110 _88266 _88270 f y x) = ((f x) = y).
Proof. exact (eq_refl (term110 _88266 _88270 f y x)). Qed.
Lemma lem3398422 {_88266 : Type'} (t : _88266 -> Prop) (y : _88266) : (term70 _88266 t y) = (term70 _88266 t y).
Proof. exact (eq_refl (term70 _88266 t y)). Qed.
Lemma lem3398423 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88270) (y : _88266) : (term115 _88266 _88270 t f y x) = (term116 _88266 _88270 t f x y).
Proof. exact (MK_COMB (@lem3398422 _88266 t y) (@lem3398421 _88266 _88270 f x y)). Qed.
Lemma lem3398424 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term117 _88266 _88270 t f y) = (term118 _88266 _88270 t f y).
Proof. exact (fun_ext (fun x : _88270 => @lem3398423 _88266 _88270 t f x y)). Qed.
Lemma lem3398425 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398426 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term108 _88266 _88270 t f y) = (term119 _88266 _88270 t f y).
Proof. exact (MK_COMB (@lem3398425 _88270) (@lem3398424 _88266 _88270 t f y)). Qed.
Lemma lem3398427 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : ((term107 _88266 _88270 t f y) = (term108 _88266 _88270 t f y)) = ((term71 _88266 _88270 t f y) = (term119 _88266 _88270 t f y)).
Proof. exact (MK_COMB (@lem3398420 _88266 _88270 t f y) (@lem3398426 _88266 _88270 t f y)). Qed.
Lemma lem3398428 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term71 _88266 _88270 t f y) = (term119 _88266 _88270 t f y).
Proof. exact (EQ_MP (@lem3398427 _88266 _88270 t f y) (@lem3398412 _88266 _88270 t f y)). Qed.
Lemma lem3398429 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term72 _88266 _88270 t f) = (term120 _88266 _88270 t f).
Proof. exact (fun_ext (fun y : _88266 => @lem3398428 _88266 _88270 t f y)). Qed.
Lemma lem3398430 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398431 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term73 _88266 _88270 t f) = (term121 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398430 _88266) (@lem3398429 _88266 _88270 t f)). Qed.
Lemma lem3398433 {A B : Type'} (P : type1413 A B) : (term122 A B P) = (term123 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3398434 {_88266 _88270 : Type'} (P : type1413 _88266 _88270) : (term122 _88266 _88270 P) = (term123 _88266 _88270 P).
Proof. exact (@lem3398433 _88266 _88270 P). Qed.
Lemma lem3398435 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term124 _88266 _88270 t f) = (term125 _88266 _88270 t f).
Proof. exact (@lem3398434 _88266 _88270 (term126 _88266 _88270 t f)). Qed.
Lemma lem3398436 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term127 _88266 _88270 t f y) = (term118 _88266 _88270 t f y).
Proof. exact (eq_refl (term127 _88266 _88270 t f y)). Qed.
Lemma lem3398437 {_88270 : Type'} (x : _88270) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3398438 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) (x : _88270) : (term128 _88266 _88270 t f y x) = (term129 _88266 _88270 t f y x).
Proof. exact (MK_COMB (@lem3398436 _88266 _88270 t f y) (@lem3398437 _88270 x)). Qed.
Lemma lem3398439 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88270) (y : _88266) : (term129 _88266 _88270 t f y x) = (term116 _88266 _88270 t f x y).
Proof. exact (eq_refl (term129 _88266 _88270 t f y x)). Qed.
Lemma lem3398440 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88270) (y : _88266) : (term128 _88266 _88270 t f y x) = (term116 _88266 _88270 t f x y).
Proof. exact (TRANS (@lem3398438 _88266 _88270 t f y x) (@lem3398439 _88266 _88270 t f x y)). Qed.
Lemma lem3398441 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term130 _88266 _88270 t f y) = (term118 _88266 _88270 t f y).
Proof. exact (fun_ext (fun x : _88270 => @lem3398440 _88266 _88270 t f x y)). Qed.
Lemma lem3398442 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398443 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term131 _88266 _88270 t f y) = (term119 _88266 _88270 t f y).
Proof. exact (MK_COMB (@lem3398442 _88270) (@lem3398441 _88266 _88270 t f y)). Qed.
Lemma lem3398444 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term132 _88266 _88270 t f) = (term120 _88266 _88270 t f).
Proof. exact (fun_ext (fun y : _88266 => @lem3398443 _88266 _88270 t f y)). Qed.
Lemma lem3398445 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398446 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term124 _88266 _88270 t f) = (term121 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398445 _88266) (@lem3398444 _88266 _88270 t f)). Qed.
Lemma lem3398447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3398448 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term133 _88266 _88270 t f) = (term134 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398447) (@lem3398446 _88266 _88270 t f)). Qed.
Lemma lem3398449 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (y : _88266) : (term127 _88266 _88270 t f y) = (term118 _88266 _88270 t f y).
Proof. exact (eq_refl (term127 _88266 _88270 t f y)). Qed.
Lemma lem3398450 {_88266 _88270 : Type'} (x : _88266 -> _88270) (y : _88266) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3398451 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) (y : _88266) : (term135 _88266 _88270 t f x y) = (term136 _88266 _88270 t f x y).
Proof. exact (MK_COMB (@lem3398449 _88266 _88270 t f y) (@lem3398450 _88266 _88270 x y)). Qed.
Lemma lem3398452 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) (y : _88266) : (term136 _88266 _88270 t f x y) = (term137 _88266 _88270 t f x y).
Proof. exact (eq_refl (term136 _88266 _88270 t f x y)). Qed.
Lemma lem3398453 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) (y : _88266) : (term135 _88266 _88270 t f x y) = (term137 _88266 _88270 t f x y).
Proof. exact (TRANS (@lem3398451 _88266 _88270 t f x y) (@lem3398452 _88266 _88270 t f x y)). Qed.
Lemma lem3398454 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) : (term138 _88266 _88270 t f x) = (term139 _88266 _88270 t f x).
Proof. exact (fun_ext (fun y : _88266 => @lem3398453 _88266 _88270 t f x y)). Qed.
Lemma lem3398455 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398456 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) : (term140 _88266 _88270 t f x) = (term141 _88266 _88270 t f x).
Proof. exact (MK_COMB (@lem3398455 _88266) (@lem3398454 _88266 _88270 t f x)). Qed.
Lemma lem3398457 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term142 _88266 _88270 t f) = (term143 _88266 _88270 t f).
Proof. exact (fun_ext (fun x : _88266 -> _88270 => @lem3398456 _88266 _88270 t f x)). Qed.
Lemma lem3398458 {_88266 _88270 : Type'} : (@ex (_88266 -> _88270)) = (@ex (_88266 -> _88270)).
Proof. exact (eq_refl (@ex (_88266 -> _88270))). Qed.
Lemma lem3398459 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term125 _88266 _88270 t f) = (term144 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398458 _88266 _88270) (@lem3398457 _88266 _88270 t f)). Qed.
Lemma lem3398460 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : ((term124 _88266 _88270 t f) = (term125 _88266 _88270 t f)) = ((term121 _88266 _88270 t f) = (term144 _88266 _88270 t f)).
Proof. exact (MK_COMB (@lem3398448 _88266 _88270 t f) (@lem3398459 _88266 _88270 t f)). Qed.
Lemma lem3398461 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term121 _88266 _88270 t f) = (term144 _88266 _88270 t f).
Proof. exact (EQ_MP (@lem3398460 _88266 _88270 t f) (@lem3398435 _88266 _88270 t f)). Qed.
Lemma lem3398462 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term73 _88266 _88270 t f) = (term144 _88266 _88270 t f).
Proof. exact (TRANS (@lem3398431 _88266 _88270 t f) (@lem3398461 _88266 _88270 t f)). Qed.
Lemma lem3398463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398464 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term77 _88266 _88270 t f) = (term145 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398463) (@lem3398462 _88266 _88270 t f)). Qed.
Lemma lem3398465 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term103 _88266 _88270 t f s) = (term103 _88266 _88270 t f s).
Proof. exact (eq_refl (term103 _88266 _88270 t f s)). Qed.
Lemma lem3398466 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term104 _88266 _88270 t f s) = (term146 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398464 _88266 _88270 t f) (@lem3398465 _88266 _88270 t f s)). Qed.
Lemma lem3398468 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3398469 {_88266 _88270 : Type'} (P : type572 _88266 _88270) (Q : Prop) : (term149 _88266 _88270 P Q) = (term150 _88266 _88270 P Q).
Proof. exact (@lem3398468 (_88266 -> _88270) P Q). Qed.
Lemma lem3398470 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term151 _88266 _88270 t f s) = (term152 _88266 _88270 t f s).
Proof. exact (@lem3398469 _88266 _88270 (term143 _88266 _88270 t f) (term103 _88266 _88270 t f s)). Qed.
Lemma lem3398471 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) : (term153 _88266 _88270 t f x) = (term141 _88266 _88270 t f x).
Proof. exact (eq_refl (term153 _88266 _88270 t f x)). Qed.
Lemma lem3398472 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term154 _88266 _88270 t f) = (term143 _88266 _88270 t f).
Proof. exact (fun_ext (fun x : _88266 -> _88270 => @lem3398471 _88266 _88270 t f x)). Qed.
Lemma lem3398473 {_88266 _88270 : Type'} : (@ex (_88266 -> _88270)) = (@ex (_88266 -> _88270)).
Proof. exact (eq_refl (@ex (_88266 -> _88270))). Qed.
Lemma lem3398474 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term155 _88266 _88270 t f) = (term144 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398473 _88266 _88270) (@lem3398472 _88266 _88270 t f)). Qed.
Lemma lem3398475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398476 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) : (term156 _88266 _88270 t f) = (term145 _88266 _88270 t f).
Proof. exact (MK_COMB (@lem3398475) (@lem3398474 _88266 _88270 t f)). Qed.
Lemma lem3398477 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term103 _88266 _88270 t f s) = (term103 _88266 _88270 t f s).
Proof. exact (eq_refl (term103 _88266 _88270 t f s)). Qed.
Lemma lem3398478 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term151 _88266 _88270 t f s) = (term146 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398476 _88266 _88270 t f) (@lem3398477 _88266 _88270 t f s)). Qed.
Lemma lem3398479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3398480 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term157 _88266 _88270 t f s) = (term158 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398479) (@lem3398478 _88266 _88270 t f s)). Qed.
Lemma lem3398481 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) : (term153 _88266 _88270 t f x) = (term141 _88266 _88270 t f x).
Proof. exact (eq_refl (term153 _88266 _88270 t f x)). Qed.
Lemma lem3398482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398483 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x : _88266 -> _88270) : (term159 _88266 _88270 t f x) = (term160 _88266 _88270 t f x).
Proof. exact (MK_COMB (@lem3398482) (@lem3398481 _88266 _88270 t f x)). Qed.
Lemma lem3398484 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term103 _88266 _88270 t f s) = (term103 _88266 _88270 t f s).
Proof. exact (eq_refl (term103 _88266 _88270 t f s)). Qed.
Lemma lem3398485 {_88266 _88270 : Type'} (x : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term161 _88266 _88270 x t f s) = (term162 _88266 _88270 x t f s).
Proof. exact (MK_COMB (@lem3398483 _88266 _88270 t f x) (@lem3398484 _88266 _88270 t f s)). Qed.
Lemma lem3398486 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term163 _88266 _88270 t f s) = (term164 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88266 -> _88270 => @lem3398485 _88266 _88270 x t f s)). Qed.
Lemma lem3398487 {_88266 _88270 : Type'} : (@ex (_88266 -> _88270)) = (@ex (_88266 -> _88270)).
Proof. exact (eq_refl (@ex (_88266 -> _88270))). Qed.
Lemma lem3398488 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term152 _88266 _88270 t f s) = (term165 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398487 _88266 _88270) (@lem3398486 _88266 _88270 t f s)). Qed.
Lemma lem3398489 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : ((term151 _88266 _88270 t f s) = (term152 _88266 _88270 t f s)) = ((term146 _88266 _88270 t f s) = (term165 _88266 _88270 t f s)).
Proof. exact (MK_COMB (@lem3398480 _88266 _88270 t f s) (@lem3398488 _88266 _88270 t f s)). Qed.
Lemma lem3398490 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term146 _88266 _88270 t f s) = (term165 _88266 _88270 t f s).
Proof. exact (EQ_MP (@lem3398489 _88266 _88270 t f s) (@lem3398470 _88266 _88270 t f s)). Qed.
Lemma lem3398491 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term104 _88266 _88270 t f s) = (term165 _88266 _88270 t f s).
Proof. exact (TRANS (@lem3398466 _88266 _88270 t f s) (@lem3398490 _88266 _88270 t f s)). Qed.
Lemma lem3398492 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term78 _88266 _88270 t f s) = (term165 _88266 _88270 t f s).
Proof. exact (TRANS (@lem3398408 _88266 _88270 t f s) (@lem3398491 _88266 _88270 t f s)). Qed.
Lemma lem3398493 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term33 _88266 _88270 t f s) = (term165 _88266 _88270 t f s).
Proof. exact (TRANS (@lem3398247 _88266 _88270 t f s) (@lem3398492 _88266 _88270 t f s)). Qed.
Lemma lem3398494 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term33 _88266 _88270 t f s) : term165 _88266 _88270 t f s.
Proof. exact (EQ_MP (@lem3398493 _88266 _88270 t f s) (@lem3398208 _88266 _88270 t f s h1)). Qed.
Lemma lem3398503 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term166 _88266 _88270 x f s x') = (term167 _88266 _88270 x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3398506 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term41 _88266 _88270 x f s x') = (term41 _88266 _88270 x f s x').
Proof. exact (eq_refl (term41 _88266 _88270 x f s x')). Qed.
Lemma lem3398507 {_88270 : Type'} (P : _88270 -> Prop) : (term168 _88270 P) = (term169 _88270 P).
Proof. exact (@lem18394 _88270 P). Qed.
Lemma lem3398508 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term170 _88266 _88270 x f s) = (term171 _88266 _88270 x f s).
Proof. exact (@lem3398507 _88270 (term43 _88266 _88270 x f s)). Qed.
Lemma lem3398509 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term172 _88266 _88270 x f s x') = (term41 _88266 _88270 x f s x').
Proof. exact (eq_refl (term172 _88266 _88270 x f s x')). Qed.
Lemma lem3398510 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3398511 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term173 _88266 _88270 x f s x') = (term166 _88266 _88270 x f s x').
Proof. exact (MK_COMB (@lem3398510) (@lem3398509 _88266 _88270 x f s x')). Qed.
Lemma lem3398512 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term173 _88266 _88270 x f s x') = (term167 _88266 _88270 x f s x').
Proof. exact (TRANS (@lem3398511 _88266 _88270 x f s x') (@lem3398503 _88266 _88270 x f s x')). Qed.
Lemma lem3398513 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term174 _88266 _88270 x f s) = (term175 _88266 _88270 x f s).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398512 _88266 _88270 x f s x')). Qed.
Lemma lem3398514 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398515 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term171 _88266 _88270 x f s) = (term176 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398514 _88270) (@lem3398513 _88266 _88270 x f s)). Qed.
Lemma lem3398516 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term170 _88266 _88270 x f s) = (term176 _88266 _88270 x f s).
Proof. exact (TRANS (@lem3398508 _88266 _88270 x f s) (@lem3398515 _88266 _88270 x f s)). Qed.
Lemma lem3398517 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term43 _88266 _88270 x f s) = (term43 _88266 _88270 x f s).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398506 _88266 _88270 x f s x')). Qed.
Lemma lem3398518 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398519 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term44 _88266 _88270 x f s) = (term44 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398518 _88270) (@lem3398517 _88266 _88270 x f s)). Qed.
Lemma lem3398520 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term109 _88266 t x) = (term109 _88266 t x).
Proof. exact (eq_refl (term109 _88266 t x)). Qed.
Lemma lem3398521 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3398522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398523 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term177 _88266 _88270 x f s) = (term178 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398522) (@lem3398516 _88266 _88270 x f s)). Qed.
Lemma lem3398524 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term179 _88266 _88270 f s t x) = (term180 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398523 _88266 _88270 x f s) (@lem3398521 _88266 t x)). Qed.
Lemma lem3398525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398526 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term181 _88266 _88270 x f s) = (term181 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398525) (@lem3398519 _88266 _88270 x f s)). Qed.
Lemma lem3398527 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term182 _88266 _88270 f s t x) = (term182 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398526 _88266 _88270 x f s) (@lem3398520 _88266 t x)). Qed.
Lemma lem3398528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3398529 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term183 _88266 _88270 f s t x) = (term183 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398528) (@lem3398527 _88266 _88270 f s t x)). Qed.
Lemma lem3398530 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term184 _88266 _88270 f s t x) = (term185 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398529 _88266 _88270 f s t x) (@lem3398524 _88266 _88270 f s t x)). Qed.
Lemma lem3398531 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term69 _88266 _88270 f s t x) = (term184 _88266 _88270 f s t x).
Proof. exact (@lem17646 (term44 _88266 _88270 x f s) (t x)). Qed.
Lemma lem3398532 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term69 _88266 _88270 f s t x) = (term185 _88266 _88270 f s t x).
Proof. exact (TRANS (@lem3398531 _88266 _88270 f s t x) (@lem3398530 _88266 _88270 f s t x)). Qed.
Lemma lem3398615 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3398616 {_88270 : Type'} (P : _88270 -> Prop) (Q : Prop) : (term147 _88270 P Q) = (term148 _88270 P Q).
Proof. exact (@lem3398615 _88270 P Q). Qed.
Lemma lem3398617 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term186 _88266 _88270 f s t x) = (term187 _88266 _88270 f s t x).
Proof. exact (@lem3398616 _88270 (term43 _88266 _88270 x f s) (term109 _88266 t x)). Qed.
Lemma lem3398618 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term172 _88266 _88270 x f s x') = (term41 _88266 _88270 x f s x').
Proof. exact (eq_refl (term172 _88266 _88270 x f s x')). Qed.
Lemma lem3398619 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term188 _88266 _88270 x f s) = (term43 _88266 _88270 x f s).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398618 _88266 _88270 x f s x')). Qed.
Lemma lem3398620 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398621 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term189 _88266 _88270 x f s) = (term44 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398620 _88270) (@lem3398619 _88266 _88270 x f s)). Qed.
Lemma lem3398622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398623 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term190 _88266 _88270 x f s) = (term181 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398622) (@lem3398621 _88266 _88270 x f s)). Qed.
Lemma lem3398624 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term109 _88266 t x) = (term109 _88266 t x).
Proof. exact (eq_refl (term109 _88266 t x)). Qed.
Lemma lem3398625 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term186 _88266 _88270 f s t x) = (term182 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398623 _88266 _88270 x f s) (@lem3398624 _88266 t x)). Qed.
Lemma lem3398626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3398627 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term191 _88266 _88270 f s t x) = (term192 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398626) (@lem3398625 _88266 _88270 f s t x)). Qed.
Lemma lem3398628 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term172 _88266 _88270 x f s x') = (term41 _88266 _88270 x f s x').
Proof. exact (eq_refl (term172 _88266 _88270 x f s x')). Qed.
Lemma lem3398629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398630 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term193 _88266 _88270 x f s x') = (term194 _88266 _88270 x f s x').
Proof. exact (MK_COMB (@lem3398629) (@lem3398628 _88266 _88270 x f s x')). Qed.
Lemma lem3398631 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term109 _88266 t x) = (term109 _88266 t x).
Proof. exact (eq_refl (term109 _88266 t x)). Qed.
Lemma lem3398632 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) (t : _88266 -> Prop) (x' : _88266) : (term195 _88266 _88270 f s x t x') = (term196 _88266 _88270 f s x t x').
Proof. exact (MK_COMB (@lem3398630 _88266 _88270 x' f s x) (@lem3398631 _88266 t x')). Qed.
Lemma lem3398633 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term197 _88266 _88270 f s t x) = (term198 _88266 _88270 f s t x).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398632 _88266 _88270 f s x' t x)). Qed.
Lemma lem3398634 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398635 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term187 _88266 _88270 f s t x) = (term199 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398634 _88270) (@lem3398633 _88266 _88270 f s t x)). Qed.
Lemma lem3398636 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : ((term186 _88266 _88270 f s t x) = (term187 _88266 _88270 f s t x)) = ((term182 _88266 _88270 f s t x) = (term199 _88266 _88270 f s t x)).
Proof. exact (MK_COMB (@lem3398627 _88266 _88270 f s t x) (@lem3398635 _88266 _88270 f s t x)). Qed.
Lemma lem3398637 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term182 _88266 _88270 f s t x) = (term199 _88266 _88270 f s t x).
Proof. exact (EQ_MP (@lem3398636 _88266 _88270 f s t x) (@lem3398617 _88266 _88270 f s t x)). Qed.
Lemma lem3398638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3398639 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term183 _88266 _88270 f s t x) = (term200 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398638) (@lem3398637 _88266 _88270 f s t x)). Qed.
Lemma lem3398640 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term180 _88266 _88270 f s t x) = (term180 _88266 _88270 f s t x).
Proof. exact (eq_refl (term180 _88266 _88270 f s t x)). Qed.
Lemma lem3398641 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term185 _88266 _88270 f s t x) = (term201 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398639 _88266 _88270 f s t x) (@lem3398640 _88266 _88270 f s t x)). Qed.
Lemma lem3398643 {A : Type'} (P : A -> Prop) (Q : Prop) : (term202 A P Q) = (term203 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3398644 {_88270 : Type'} (P : _88270 -> Prop) (Q : Prop) : (term202 _88270 P Q) = (term203 _88270 P Q).
Proof. exact (@lem3398643 _88270 P Q). Qed.
Lemma lem3398645 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term204 _88266 _88270 f s t x) = (term205 _88266 _88270 f s t x).
Proof. exact (@lem3398644 _88270 (term198 _88266 _88270 f s t x) (term180 _88266 _88270 f s t x)). Qed.
Lemma lem3398646 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) (t : _88266 -> Prop) (x' : _88266) : (term206 _88266 _88270 f s t x' x) = (term196 _88266 _88270 f s x t x').
Proof. exact (eq_refl (term206 _88266 _88270 f s t x' x)). Qed.
Lemma lem3398647 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term207 _88266 _88270 f s t x) = (term198 _88266 _88270 f s t x).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398646 _88266 _88270 f s x' t x)). Qed.
Lemma lem3398648 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398649 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term208 _88266 _88270 f s t x) = (term199 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398648 _88270) (@lem3398647 _88266 _88270 f s t x)). Qed.
Lemma lem3398650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3398651 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term209 _88266 _88270 f s t x) = (term200 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398650) (@lem3398649 _88266 _88270 f s t x)). Qed.
Lemma lem3398652 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term180 _88266 _88270 f s t x) = (term180 _88266 _88270 f s t x).
Proof. exact (eq_refl (term180 _88266 _88270 f s t x)). Qed.
Lemma lem3398653 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term204 _88266 _88270 f s t x) = (term201 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398651 _88266 _88270 f s t x) (@lem3398652 _88266 _88270 f s t x)). Qed.
Lemma lem3398654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3398655 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term210 _88266 _88270 f s t x) = (term211 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398654) (@lem3398653 _88266 _88270 f s t x)). Qed.
Lemma lem3398656 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) (t : _88266 -> Prop) (x' : _88266) : (term206 _88266 _88270 f s t x' x) = (term196 _88266 _88270 f s x t x').
Proof. exact (eq_refl (term206 _88266 _88270 f s t x' x)). Qed.
Lemma lem3398657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3398658 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) (t : _88266 -> Prop) (x' : _88266) : (term212 _88266 _88270 f s t x' x) = (term213 _88266 _88270 f s x t x').
Proof. exact (MK_COMB (@lem3398657) (@lem3398656 _88266 _88270 f s x t x')). Qed.
Lemma lem3398659 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term180 _88266 _88270 f s t x) = (term180 _88266 _88270 f s t x).
Proof. exact (eq_refl (term180 _88266 _88270 f s t x)). Qed.
Lemma lem3398660 {_88266 _88270 : Type'} (x : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x' : _88266) : (term214 _88266 _88270 x f s t x') = (term215 _88266 _88270 x f s t x').
Proof. exact (MK_COMB (@lem3398658 _88266 _88270 f s x t x') (@lem3398659 _88266 _88270 f s t x')). Qed.
Lemma lem3398661 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term216 _88266 _88270 f s t x) = (term217 _88266 _88270 f s t x).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398660 _88266 _88270 x' f s t x)). Qed.
Lemma lem3398662 {_88270 : Type'} : (@ex _88270) = (@ex _88270).
Proof. exact (eq_refl (@ex _88270)). Qed.
Lemma lem3398663 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term205 _88266 _88270 f s t x) = (term218 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398662 _88270) (@lem3398661 _88266 _88270 f s t x)). Qed.
Lemma lem3398664 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : ((term204 _88266 _88270 f s t x) = (term205 _88266 _88270 f s t x)) = ((term201 _88266 _88270 f s t x) = (term218 _88266 _88270 f s t x)).
Proof. exact (MK_COMB (@lem3398655 _88266 _88270 f s t x) (@lem3398663 _88266 _88270 f s t x)). Qed.
Lemma lem3398665 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term201 _88266 _88270 f s t x) = (term218 _88266 _88270 f s t x).
Proof. exact (EQ_MP (@lem3398664 _88266 _88270 f s t x) (@lem3398645 _88266 _88270 f s t x)). Qed.
Lemma lem3398667 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term185 _88266 _88270 f s t x) = (term218 _88266 _88270 f s t x).
Proof. exact (TRANS (@lem3398641 _88266 _88270 f s t x) (@lem3398665 _88266 _88270 f s t x)). Qed.
Lemma lem3398668 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term69 _88266 _88270 f s t x) = (term218 _88266 _88270 f s t x).
Proof. exact (TRANS (@lem3398532 _88266 _88270 f s t x) (@lem3398667 _88266 _88270 f s t x)). Qed.
Lemma lem3398669 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term69 _88266 _88270 f s t x) : term218 _88266 _88270 f s t x.
Proof. exact (EQ_MP (@lem3398668 _88266 _88270 f s t x) (@lem3398213 _88266 _88270 f s t x h1)). Qed.
Lemma lem3398670 {_88266 _88270 : Type'} (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term215 _88266 _88270 x' f s t x) : term215 _88266 _88270 x' f s t x.
Proof. exact (h1). Qed.
Lemma lem3398671 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term162 _88266 _88270 x'' t f s.
Proof. exact (h1). Qed.
Lemma lem3398674 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3398691 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term167 _88266 _88270 x f s x') = (term167 _88266 _88270 x f s x').
Proof. exact (eq_refl (term167 _88266 _88270 x f s x')). Qed.
Lemma lem3398692 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term175 _88266 _88270 x f s) = (term175 _88266 _88270 x f s).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398691 _88266 _88270 x f s x')). Qed.
Lemma lem3398693 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398694 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term176 _88266 _88270 x f s) = (term176 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398693 _88270) (@lem3398692 _88266 _88270 x f s)). Qed.
Lemma lem3398695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398696 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term178 _88266 _88270 x f s) = (term178 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398695) (@lem3398694 _88266 _88270 x f s)). Qed.
Lemma lem3398697 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term180 _88266 _88270 f s t x) = (term180 _88266 _88270 f s t x).
Proof. exact (MK_COMB (@lem3398696 _88266 _88270 x f s) (@lem3398674 _88266 t x)). Qed.
Lemma lem3398720 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) : (term213 _88266 _88270 f s x' t x) = (term213 _88266 _88270 f s x' t x).
Proof. exact (eq_refl (term213 _88266 _88270 f s x' t x)). Qed.
Lemma lem3398721 {_88266 _88270 : Type'} (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) : (term215 _88266 _88270 x' f s t x) = (term215 _88266 _88270 x' f s t x).
Proof. exact (MK_COMB (@lem3398720 _88266 _88270 f s x' t x) (@lem3398697 _88266 _88270 f s t x)). Qed.
Lemma lem3398722 {_88266 _88270 : Type'} (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term215 _88266 _88270 x' f s t x) : term215 _88266 _88270 x' f s t x.
Proof. exact (EQ_MP (@lem3398721 _88266 _88270 x' f s t x) (@lem3398670 _88266 _88270 x' f s t x h1)). Qed.
Lemma lem3398735 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term90 _88266 _88270 t f s x) = (term90 _88266 _88270 t f s x).
Proof. exact (eq_refl (term90 _88266 _88270 t f s x)). Qed.
Lemma lem3398736 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term84 _88266 _88270 t f s) = (term84 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398735 _88266 _88270 t f s x)). Qed.
Lemma lem3398737 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398738 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term102 _88266 _88270 t f s) = (term102 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398737 _88270) (@lem3398736 _88266 _88270 t f s)). Qed.
Lemma lem3398751 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term86 _88266 _88270 t f s x) = (term86 _88266 _88270 t f s x).
Proof. exact (eq_refl (term86 _88266 _88270 t f s x)). Qed.
Lemma lem3398752 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term83 _88266 _88270 t f s) = (term83 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398751 _88266 _88270 t f s x)). Qed.
Lemma lem3398753 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398754 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term97 _88266 _88270 t f s) = (term97 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398753 _88270) (@lem3398752 _88266 _88270 t f s)). Qed.
Lemma lem3398755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398756 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term99 _88266 _88270 t f s) = (term99 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398755) (@lem3398754 _88266 _88270 t f s)). Qed.
Lemma lem3398757 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term103 _88266 _88270 t f s) = (term103 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398756 _88266 _88270 t f s) (@lem3398738 _88266 _88270 t f s)). Qed.
Lemma lem3398774 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (y : _88266) : (term137 _88266 _88270 t f x'' y) = (term137 _88266 _88270 t f x'' y).
Proof. exact (eq_refl (term137 _88266 _88270 t f x'' y)). Qed.
Lemma lem3398775 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) : (term139 _88266 _88270 t f x'') = (term139 _88266 _88270 t f x'').
Proof. exact (fun_ext (fun y : _88266 => @lem3398774 _88266 _88270 t f x'' y)). Qed.
Lemma lem3398776 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398777 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) : (term141 _88266 _88270 t f x'') = (term141 _88266 _88270 t f x'').
Proof. exact (MK_COMB (@lem3398776 _88266) (@lem3398775 _88266 _88270 t f x'')). Qed.
Lemma lem3398778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3398779 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) : (term160 _88266 _88270 t f x'') = (term160 _88266 _88270 t f x'').
Proof. exact (MK_COMB (@lem3398778) (@lem3398777 _88266 _88270 t f x'')). Qed.
Lemma lem3398780 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term162 _88266 _88270 x'' t f s) = (term162 _88266 _88270 x'' t f s).
Proof. exact (MK_COMB (@lem3398779 _88266 _88270 t f x'') (@lem3398757 _88266 _88270 t f s)). Qed.
Lemma lem3398781 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term162 _88266 _88270 x'' t f s.
Proof. exact (EQ_MP (@lem3398780 _88266 _88270 x'' t f s) (@lem3398671 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398782 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term103 _88266 _88270 t f s.
Proof. exact (proj2 (@lem3398781 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398783 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term141 _88266 _88270 t f x''.
Proof. exact (proj1 (@lem3398781 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398784 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term102 _88266 _88270 t f s.
Proof. exact (proj2 (@lem3398782 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398785 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term97 _88266 _88270 t f s.
Proof. exact (proj1 (@lem3398782 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398786 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : term196 _88266 _88270 f s x' t x.
Proof. exact (h1). Qed.
Lemma lem3398787 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term180 _88266 _88270 f s t x.
Proof. exact (h1). Qed.
Lemma lem3398789 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : term41 _88266 _88270 x f s x'.
Proof. exact (proj1 (@lem3398786 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3398793 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term176 _88266 _88270 x f s.
Proof. exact (proj1 (@lem3398787 _88266 _88270 f s t x h1)). Qed.
Lemma lem3398814 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term86 _88266 _88270 t f s x) = (term86 _88266 _88270 t f s x).
Proof. exact (eq_refl (term86 _88266 _88270 t f s x)). Qed.
Lemma lem3398815 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term83 _88266 _88270 t f s) = (term83 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398814 _88266 _88270 t f s x)). Qed.
Lemma lem3398816 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398818 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term97 _88266 _88270 t f s) = (term97 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398816 _88270) (@lem3398815 _88266 _88270 t f s)). Qed.
Lemma lem3398819 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term97 _88266 _88270 t f s.
Proof. exact (EQ_MP (@lem3398818 _88266 _88270 t f s) (@lem3398785 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398852 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (y : _88266) : (term137 _88266 _88270 t f x'' y) = (term137 _88266 _88270 t f x'' y).
Proof. exact (eq_refl (term137 _88266 _88270 t f x'' y)). Qed.
Lemma lem3398853 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) : (term139 _88266 _88270 t f x'') = (term139 _88266 _88270 t f x'').
Proof. exact (fun_ext (fun y : _88266 => @lem3398852 _88266 _88270 t f x'' y)). Qed.
Lemma lem3398854 {_88266 : Type'} : (@all _88266) = (@all _88266).
Proof. exact (eq_refl (@all _88266)). Qed.
Lemma lem3398856 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) : (term141 _88266 _88270 t f x'') = (term141 _88266 _88270 t f x'').
Proof. exact (MK_COMB (@lem3398854 _88266) (@lem3398853 _88266 _88270 t f x'')). Qed.
Lemma lem3398857 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term141 _88266 _88270 t f x''.
Proof. exact (EQ_MP (@lem3398856 _88266 _88270 t f x'') (@lem3398783 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398878 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (x : _88270) : (term90 _88266 _88270 t f s x) = (term90 _88266 _88270 t f s x).
Proof. exact (eq_refl (term90 _88266 _88270 t f s x)). Qed.
Lemma lem3398879 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term84 _88266 _88270 t f s) = (term84 _88266 _88270 t f s).
Proof. exact (fun_ext (fun x : _88270 => @lem3398878 _88266 _88270 t f s x)). Qed.
Lemma lem3398880 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398882 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term102 _88266 _88270 t f s) = (term102 _88266 _88270 t f s).
Proof. exact (MK_COMB (@lem3398880 _88270) (@lem3398879 _88266 _88270 t f s)). Qed.
Lemma lem3398883 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term102 _88266 _88270 t f s.
Proof. exact (EQ_MP (@lem3398882 _88266 _88270 t f s) (@lem3398784 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3398891 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) : (term167 _88266 _88270 x f s x') = (term167 _88266 _88270 x f s x').
Proof. exact (eq_refl (term167 _88266 _88270 x f s x')). Qed.
Lemma lem3398892 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term175 _88266 _88270 x f s) = (term175 _88266 _88270 x f s).
Proof. exact (fun_ext (fun x' : _88270 => @lem3398891 _88266 _88270 x f s x')). Qed.
Lemma lem3398893 {_88270 : Type'} : (@all _88270) = (@all _88270).
Proof. exact (eq_refl (@all _88270)). Qed.
Lemma lem3398895 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) : (term176 _88266 _88270 x f s) = (term176 _88266 _88270 x f s).
Proof. exact (MK_COMB (@lem3398893 _88270) (@lem3398892 _88266 _88270 x f s)). Qed.
Lemma lem3398896 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term176 _88266 _88270 x f s.
Proof. exact (EQ_MP (@lem3398895 _88266 _88270 x f s) (@lem3398793 _88266 _88270 f s t x h1)). Qed.
Lemma lem3398904 {_88266 _88270 : Type'} (_35804 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term85 _88266 _88270 t f s _35804.
Proof. exact (@lem3398819 _88266 _88270 x'' t f s h1 _35804). Qed.
Lemma lem3398905 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35804 : _88270) : (term85 _88266 _88270 t f s _35804) = (term86 _88266 _88270 t f s _35804).
Proof. exact (eq_refl (term85 _88266 _88270 t f s _35804)). Qed.
Lemma lem3398910 {_88266 _88270 : Type'} (_35806 : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term219 _88266 _88270 t f x'' _35806.
Proof. exact (@lem3398857 _88266 _88270 x'' t f s h1 _35806). Qed.
Lemma lem3398911 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (_35806 : _88266) : (term219 _88266 _88270 t f x'' _35806) = (term137 _88266 _88270 t f x'' _35806).
Proof. exact (eq_refl (term219 _88266 _88270 t f x'' _35806)). Qed.
Lemma lem3398916 {_88266 _88270 : Type'} (_35808 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term89 _88266 _88270 t f s _35808.
Proof. exact (@lem3398883 _88266 _88270 x'' t f s h1 _35808). Qed.
Lemma lem3398917 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35808 : _88270) : (term89 _88266 _88270 t f s _35808) = (term90 _88266 _88270 t f s _35808).
Proof. exact (eq_refl (term89 _88266 _88270 t f s _35808)). Qed.
Lemma lem3398919 {_88266 _88270 : Type'} (_35809 : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term220 _88266 _88270 x f s _35809.
Proof. exact (@lem3398896 _88266 _88270 f s t x h1 _35809). Qed.
Lemma lem3398920 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35809 : _88270) : (term220 _88266 _88270 x f s _35809) = (term167 _88266 _88270 x f s _35809).
Proof. exact (eq_refl (term220 _88266 _88270 x f s _35809)). Qed.
Lemma lem3398941 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : term109 _88266 t x.
Proof. exact (proj2 (@lem3398786 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3398943 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : x = (f x').
Proof. exact (proj1 (@lem3398789 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3398951 {_88266 _88270 : Type'} (_35806 : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term137 _88266 _88270 t f x'' _35806.
Proof. exact (EQ_MP (@lem3398911 _88266 _88270 t f x'' _35806) (@lem3398910 _88266 _88270 _35806 x'' t f s h1)). Qed.
Lemma lem3398963 {_88266 _88270 : Type'} (_35808 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term90 _88266 _88270 t f s _35808.
Proof. exact (EQ_MP (@lem3398917 _88266 _88270 t f s _35808) (@lem3398916 _88266 _88270 _35808 x'' t f s h1)). Qed.
Lemma lem3398969 {_88266 _88270 : Type'} (_35809 : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term167 _88266 _88270 x f s _35809.
Proof. exact (EQ_MP (@lem3398920 _88266 _88270 x f s _35809) (@lem3398919 _88266 _88270 _35809 f s t x h1)). Qed.
Lemma lem3399013 {_88266 _88270 : Type'} (_35804 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term86 _88266 _88270 t f s _35804.
Proof. exact (EQ_MP (@lem3398905 _88266 _88270 t f s _35804) (@lem3398904 _88266 _88270 _35804 x'' t f s h1)). Qed.
Lemma lem3399028 {_88266 : Type'} (t : _88266 -> Prop) : (term221 _88266 t) = (term221 _88266 t).
Proof. exact (eq_refl (term221 _88266 t)). Qed.
Lemma lem3399029 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : (term222 _88266 t x) = (term223 _88266 _88270 t f x').
Proof. exact (MK_COMB (@lem3399028 _88266 t) (@lem3398943 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3399030 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x' : _88270) : (term223 _88266 _88270 t f x') = (term224 _88266 _88270 t f x').
Proof. exact (eq_refl (term223 _88266 _88270 t f x')). Qed.
Lemma lem3399031 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term225 _88266 t x) = (term225 _88266 t x).
Proof. exact (eq_refl (term225 _88266 t x)). Qed.
Lemma lem3399032 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (x' : _88270) : ((term222 _88266 t x) = (term223 _88266 _88270 t f x')) = ((term222 _88266 t x) = (term224 _88266 _88270 t f x')).
Proof. exact (MK_COMB (@lem3399031 _88266 t x) (@lem3399030 _88266 _88270 t f x')). Qed.
Lemma lem3399033 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term222 _88266 t x) = (term109 _88266 t x).
Proof. exact (eq_refl (term222 _88266 t x)). Qed.
Lemma lem3399034 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399035 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term225 _88266 t x) = (term226 _88266 t x).
Proof. exact (MK_COMB (@lem3399034) (@lem3399033 _88266 t x)). Qed.
Lemma lem3399036 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x' : _88270) : (term224 _88266 _88270 t f x') = (term224 _88266 _88270 t f x').
Proof. exact (eq_refl (term224 _88266 _88270 t f x')). Qed.
Lemma lem3399037 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (x' : _88270) : ((term222 _88266 t x) = (term224 _88266 _88270 t f x')) = ((term109 _88266 t x) = (term224 _88266 _88270 t f x')).
Proof. exact (MK_COMB (@lem3399035 _88266 t x) (@lem3399036 _88266 _88270 t f x')). Qed.
Lemma lem3399038 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (x' : _88270) : ((term222 _88266 t x) = (term223 _88266 _88270 t f x')) = ((term109 _88266 t x) = (term224 _88266 _88270 t f x')).
Proof. exact (TRANS (@lem3399032 _88266 _88270 x t f x') (@lem3399037 _88266 _88270 x t f x')). Qed.
Lemma lem3399039 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : (term109 _88266 t x) = (term224 _88266 _88270 t f x').
Proof. exact (EQ_MP (@lem3399038 _88266 _88270 x t f x') (@lem3399029 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3399040 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : term224 _88266 _88270 t f x'.
Proof. exact (EQ_MP (@lem3399039 _88266 _88270 f s x' t x h1) (@lem3398941 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3399100 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : s x'.
Proof. exact (proj2 (@lem3398789 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3399101 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : term227 _88270 s x'.
Proof. exact (fun h0 : term109 _88270 s x' => @lem3399100 _88266 _88270 f s x' t x h1). Qed.
Lemma lem3399103 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399104 {_88270 : Type'} (s : _88270 -> Prop) (x' : _88270) : (term227 _88270 s x') = (s x').
Proof. exact (@lem3399103 (s x')). Qed.
Lemma lem3399105 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : s x'.
Proof. exact (EQ_MP (@lem3399104 _88270 s x') (@lem3399101 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3399107 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3399108 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35804 : _88270) : (term86 _88266 _88270 t f s _35804) = (term230 _88266 _88270 s t f _35804).
Proof. exact (@lem3399107 (term109 _88270 s _35804) (term25 _88266 _88270 t f _35804)). Qed.
Lemma lem3399110 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3399111 {_88270 : Type'} (s : _88270 -> Prop) (_35804 : _88270) : (term231 _88270 s _35804) = (s _35804).
Proof. exact (@lem3399110 (s _35804)). Qed.
Lemma lem3399112 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3399113 {_88270 : Type'} (s : _88270 -> Prop) (_35804 : _88270) : (term232 _88270 s _35804) = (term14 _88270 s _35804).
Proof. exact (MK_COMB (@lem3399112) (@lem3399111 _88270 s _35804)). Qed.
Lemma lem3399114 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (_35804 : _88270) : (term25 _88266 _88270 t f _35804) = (term25 _88266 _88270 t f _35804).
Proof. exact (eq_refl (term25 _88266 _88270 t f _35804)). Qed.
Lemma lem3399115 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35804 : _88270) : (term230 _88266 _88270 s t f _35804) = (term233 _88266 _88270 s t f _35804).
Proof. exact (MK_COMB (@lem3399113 _88270 s _35804) (@lem3399114 _88266 _88270 t f _35804)). Qed.
Lemma lem3399116 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35804 : _88270) : (term86 _88266 _88270 t f s _35804) = (term233 _88266 _88270 s t f _35804).
Proof. exact (TRANS (@lem3399108 _88266 _88270 s t f _35804) (@lem3399115 _88266 _88270 s t f _35804)). Qed.
Lemma lem3399119 {_88266 _88270 : Type'} (_35804 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term233 _88266 _88270 s t f _35804.
Proof. exact (EQ_MP (@lem3399116 _88266 _88270 s t f _35804) (@lem3399013 _88266 _88270 _35804 x'' t f s h1)). Qed.
Lemma lem3399120 {_88266 _88270 : Type'} (_35804 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term233 _88266 _88270 s t f _35804.
Proof. exact (@lem3399119 _88266 _88270 _35804 x'' t f s h1). Qed.
Lemma lem3399121 {_88266 _88270 : Type'} (x' : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term233 _88266 _88270 s t f x'.
Proof. exact (@lem3399120 _88266 _88270 x' x'' t f s h1). Qed.
Lemma lem3399124 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term196 _88266 _88270 f s x' t x) : term25 _88266 _88270 t f x'.
Proof. exact (@lem3399121 _88266 _88270 x' x'' t f s h1 (@lem3399105 _88266 _88270 f s x' t x h2)). Qed.
Lemma lem3399125 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term196 _88266 _88270 f s x' t x) : term234 _88266 _88270 t f x'.
Proof. exact (fun h0 : term224 _88266 _88270 t f x' => @lem3399124 _88266 _88270 x'' f s x' t x h1 h2). Qed.
Lemma lem3399127 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399128 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x' : _88270) : (term234 _88266 _88270 t f x') = (term25 _88266 _88270 t f x').
Proof. exact (@lem3399127 (term25 _88266 _88270 t f x')). Qed.
Lemma lem3399129 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term196 _88266 _88270 f s x' t x) : term25 _88266 _88270 t f x'.
Proof. exact (EQ_MP (@lem3399128 _88266 _88270 t f x') (@lem3399125 _88266 _88270 x'' f s x' t x h1 h2)). Qed.
Lemma lem3399132 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3399134 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x' : _88270) : (term224 _88266 _88270 t f x') = (term235 _88266 _88270 t f x').
Proof. exact (@lem3399132 (term25 _88266 _88270 t f x')). Qed.
Lemma lem3399137 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term196 _88266 _88270 f s x' t x) : term235 _88266 _88270 t f x'.
Proof. exact (EQ_MP (@lem3399134 _88266 _88270 t f x') (@lem3399040 _88266 _88270 f s x' t x h1)). Qed.
Lemma lem3399140 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term196 _88266 _88270 f s x' t x) : False.
Proof. exact (@lem3399137 _88266 _88270 f s x' t x h2 (@lem3399129 _88266 _88270 x'' f s x' t x h1 h2)). Qed.
Lemma lem3399141 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term196 _88266 _88270 f s x' t x) : term236.
Proof. exact (fun h0 : ~ False => @lem3399140 _88266 _88270 x'' f s x' t x h1 h2). Qed.
Lemma lem3399143 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399144 : term236 = False.
Proof. exact (@lem3399143 False). Qed.
Lemma lem3399158 {_88266 : Type'} (t : _88266 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3399159 {_88266 : Type'} (_35832 : _88266) (_35833 : _88266) (h1 : _35832 = _35833) : _35832 = _35833.
Proof. exact (h1). Qed.
Lemma lem3399160 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) (h1 : _35832 = _35833) : (t _35832) = (t _35833).
Proof. exact (MK_COMB (@lem3399158 _88266 t) (@lem3399159 _88266 _35832 _35833 h1)). Qed.
Lemma lem3399162 (b : Prop) (a : Prop) : term237 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3399163 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : term238 _88266 _35833 t _35832.
Proof. exact (@lem3399162 (t _35833) (t _35832)). Qed.
Lemma lem3399164 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) (h1 : _35832 = _35833) : term239 _88266 _35833 t _35832.
Proof. exact (@lem3399163 _88266 _35833 t _35832 (@lem3399160 _88266 t _35832 _35833 h1)). Qed.
Lemma lem3399165 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : term240 _88266 _35833 t _35832.
Proof. exact (fun h0 : _35832 = _35833 => @lem3399164 _88266 t _35832 _35833 h0). Qed.
Lemma lem3399167 (a : Prop) (b : Prop) : (a -> b) = (term241 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3399168 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : (term240 _88266 _35833 t _35832) = (term242 _88266 _35833 t _35832).
Proof. exact (@lem3399167 (_35832 = _35833) (term239 _88266 _35833 t _35832)). Qed.
Lemma lem3399169 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : term242 _88266 _35833 t _35832.
Proof. exact (EQ_MP (@lem3399168 _88266 _35833 t _35832) (@lem3399165 _88266 _35833 t _35832)). Qed.
Lemma lem3399187 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : term243 _88266 x y z.
Proof. exact (@lem21385 _88266 x y z). Qed.
Lemma lem3399191 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : t x.
Proof. exact (proj2 (@lem3398787 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399192 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term227 _88266 t x.
Proof. exact (fun h0 : term109 _88266 t x => @lem3399191 _88266 _88270 f s t x h1). Qed.
Lemma lem3399194 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399195 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term227 _88266 t x) = (t x).
Proof. exact (@lem3399194 (t x)). Qed.
Lemma lem3399196 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : t x.
Proof. exact (EQ_MP (@lem3399195 _88266 t x) (@lem3399192 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399202 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3399203 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : (term137 _88266 _88270 t f x'' _35806) = (term244 _88266 _88270 f x'' t _35806).
Proof. exact (@lem3399202 ((term245 _88266 _88270 f x'' _35806) = _35806) (term109 _88266 t _35806)). Qed.
Lemma lem3399211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399212 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : (term246 _88266 _88270 t f x'' _35806) = (term247 _88266 _88270 f x'' t _35806).
Proof. exact (MK_COMB (@lem3399211) (@lem3399203 _88266 _88270 f x'' t _35806)). Qed.
Lemma lem3399220 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : (term244 _88266 _88270 f x'' t _35806) = (term244 _88266 _88270 f x'' t _35806).
Proof. exact (eq_refl (term244 _88266 _88270 f x'' t _35806)). Qed.
Lemma lem3399221 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : ((term137 _88266 _88270 t f x'' _35806) = (term244 _88266 _88270 f x'' t _35806)) = ((term244 _88266 _88270 f x'' t _35806) = (term244 _88266 _88270 f x'' t _35806)).
Proof. exact (MK_COMB (@lem3399212 _88266 _88270 f x'' t _35806) (@lem3399220 _88266 _88270 f x'' t _35806)). Qed.
Lemma lem3399223 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3399224 (x : Prop) : (x = x) = True.
Proof. exact (@lem3399223 Prop x). Qed.
Lemma lem3399225 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : ((term244 _88266 _88270 f x'' t _35806) = (term244 _88266 _88270 f x'' t _35806)) = True.
Proof. exact (@lem3399224 (term244 _88266 _88270 f x'' t _35806)). Qed.
Lemma lem3399226 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : ((term137 _88266 _88270 t f x'' _35806) = (term244 _88266 _88270 f x'' t _35806)) = True.
Proof. exact (TRANS (@lem3399221 _88266 _88270 f x'' t _35806) (@lem3399225 _88266 _88270 f x'' t _35806)). Qed.
Lemma lem3399227 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : True = ((term137 _88266 _88270 t f x'' _35806) = (term244 _88266 _88270 f x'' t _35806)).
Proof. exact (SYM (@lem3399226 _88266 _88270 f x'' t _35806)). Qed.
Lemma lem3399228 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (_35806 : _88266) : (term137 _88266 _88270 t f x'' _35806) = (term244 _88266 _88270 f x'' t _35806).
Proof. exact (EQ_MP (@lem3399227 _88266 _88270 f x'' t _35806) (@lem0)). Qed.
Lemma lem3399229 {_88266 _88270 : Type'} (_35806 : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term244 _88266 _88270 f x'' t _35806.
Proof. exact (EQ_MP (@lem3399228 _88266 _88270 f x'' t _35806) (@lem3398951 _88266 _88270 _35806 x'' t f s h1)). Qed.
Lemma lem3399231 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3399232 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (_35806 : _88266) : (term244 _88266 _88270 f x'' t _35806) = (term248 _88266 _88270 t f x'' _35806).
Proof. exact (@lem3399231 (term109 _88266 t _35806) ((term245 _88266 _88270 f x'' _35806) = _35806)). Qed.
Lemma lem3399234 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3399235 {_88266 : Type'} (t : _88266 -> Prop) (_35806 : _88266) : (term231 _88266 t _35806) = (t _35806).
Proof. exact (@lem3399234 (t _35806)). Qed.
Lemma lem3399236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3399237 {_88266 : Type'} (t : _88266 -> Prop) (_35806 : _88266) : (term232 _88266 t _35806) = (term14 _88266 t _35806).
Proof. exact (MK_COMB (@lem3399236) (@lem3399235 _88266 t _35806)). Qed.
Lemma lem3399238 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (_35806 : _88266) : ((term245 _88266 _88270 f x'' _35806) = _35806) = ((term245 _88266 _88270 f x'' _35806) = _35806).
Proof. exact (eq_refl ((term245 _88266 _88270 f x'' _35806) = _35806)). Qed.
Lemma lem3399239 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (_35806 : _88266) : (term248 _88266 _88270 t f x'' _35806) = (term249 _88266 _88270 t f x'' _35806).
Proof. exact (MK_COMB (@lem3399237 _88266 t _35806) (@lem3399238 _88266 _88270 f x'' _35806)). Qed.
Lemma lem3399240 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (_35806 : _88266) : (term244 _88266 _88270 f x'' t _35806) = (term249 _88266 _88270 t f x'' _35806).
Proof. exact (TRANS (@lem3399232 _88266 _88270 t f x'' _35806) (@lem3399239 _88266 _88270 t f x'' _35806)). Qed.
Lemma lem3399243 {_88266 _88270 : Type'} (_35806 : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term249 _88266 _88270 t f x'' _35806.
Proof. exact (EQ_MP (@lem3399240 _88266 _88270 t f x'' _35806) (@lem3399229 _88266 _88270 _35806 x'' t f s h1)). Qed.
Lemma lem3399244 {_88266 _88270 : Type'} (_35806 : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term249 _88266 _88270 t f x'' _35806.
Proof. exact (@lem3399243 _88266 _88270 _35806 x'' t f s h1). Qed.
Lemma lem3399245 {_88266 _88270 : Type'} (x : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term249 _88266 _88270 t f x'' x.
Proof. exact (@lem3399244 _88266 _88270 x x'' t f s h1). Qed.
Lemma lem3399248 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : (term245 _88266 _88270 f x'' x) = x.
Proof. exact (@lem3399245 _88266 _88270 x x'' t f s h1 (@lem3399196 _88266 _88270 f s t x h2)). Qed.
Lemma lem3399249 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term250 _88266 _88270 f x'' x.
Proof. exact (fun h0 : term251 _88266 _88270 f x'' x => @lem3399248 _88266 _88270 x'' f s t x h1 h2). Qed.
Lemma lem3399251 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399252 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term250 _88266 _88270 f x'' x) = ((term245 _88266 _88270 f x'' x) = x).
Proof. exact (@lem3399251 ((term245 _88266 _88270 f x'' x) = x)). Qed.
Lemma lem3399253 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : (term245 _88266 _88270 f x'' x) = x.
Proof. exact (EQ_MP (@lem3399252 _88266 _88270 f x'' x) (@lem3399249 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399255 {_88266 : Type'} (x : _88266) : x = x.
Proof. exact (@lem21386 _88266 x). Qed.
Lemma lem3399256 {_88266 : Type'} (x : _88266) : x = x.
Proof. exact (@lem3399255 _88266 x). Qed.
Lemma lem3399257 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x).
Proof. exact (@lem3399256 _88266 (term245 _88266 _88270 f x'' x)). Qed.
Lemma lem3399258 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : term252 _88266 _88270 f x'' x.
Proof. exact (fun h0 : term253 _88266 _88270 f x'' x => @lem3399257 _88266 _88270 f x'' x). Qed.
Lemma lem3399260 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399261 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term252 _88266 _88270 f x'' x) = ((term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x)).
Proof. exact (@lem3399260 ((term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x))). Qed.
Lemma lem3399262 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x).
Proof. exact (EQ_MP (@lem3399261 _88266 _88270 f x'' x) (@lem3399258 _88266 _88270 f x'' x)). Qed.
Lemma lem3399280 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3399281 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term254 _88266 x y z) = (term255 _88266 y x z).
Proof. exact (@lem3399280 (y = z) (term256 _88266 x z)). Qed.
Lemma lem3399291 {_88266 : Type'} (x : _88266) (y : _88266) : (term257 _88266 x y) = (term257 _88266 x y).
Proof. exact (eq_refl (term257 _88266 x y)). Qed.
Lemma lem3399292 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term243 _88266 x y z) = (term258 _88266 y x z).
Proof. exact (MK_COMB (@lem3399291 _88266 x y) (@lem3399281 _88266 y x z)). Qed.
Lemma lem3399296 (q : Prop) (p : Prop) (r : Prop) : (term259 p q r) = (term259 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3399297 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term258 _88266 y x z) = (term260 _88266 y x z).
Proof. exact (@lem3399296 (y = z) (term256 _88266 x y) (term256 _88266 x z)). Qed.
Lemma lem3399319 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term243 _88266 x y z) = (term260 _88266 y x z).
Proof. exact (TRANS (@lem3399292 _88266 y x z) (@lem3399297 _88266 y x z)). Qed.
Lemma lem3399320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399321 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term261 _88266 x y z) = (term262 _88266 y x z).
Proof. exact (MK_COMB (@lem3399320) (@lem3399319 _88266 y x z)). Qed.
Lemma lem3399343 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term260 _88266 y x z) = (term260 _88266 y x z).
Proof. exact (eq_refl (term260 _88266 y x z)). Qed.
Lemma lem3399344 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : ((term243 _88266 x y z) = (term260 _88266 y x z)) = ((term260 _88266 y x z) = (term260 _88266 y x z)).
Proof. exact (MK_COMB (@lem3399321 _88266 y x z) (@lem3399343 _88266 y x z)). Qed.
Lemma lem3399346 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3399347 (x : Prop) : (x = x) = True.
Proof. exact (@lem3399346 Prop x). Qed.
Lemma lem3399348 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : ((term260 _88266 y x z) = (term260 _88266 y x z)) = True.
Proof. exact (@lem3399347 (term260 _88266 y x z)). Qed.
Lemma lem3399349 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : ((term243 _88266 x y z) = (term260 _88266 y x z)) = True.
Proof. exact (TRANS (@lem3399344 _88266 y x z) (@lem3399348 _88266 y x z)). Qed.
Lemma lem3399350 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : True = ((term243 _88266 x y z) = (term260 _88266 y x z)).
Proof. exact (SYM (@lem3399349 _88266 y x z)). Qed.
Lemma lem3399351 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term243 _88266 x y z) = (term260 _88266 y x z).
Proof. exact (EQ_MP (@lem3399350 _88266 y x z) (@lem0)). Qed.
Lemma lem3399352 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : term260 _88266 y x z.
Proof. exact (EQ_MP (@lem3399351 _88266 y x z) (@lem3399187 _88266 x y z)). Qed.
Lemma lem3399354 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3399355 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : (term260 _88266 y x z) = (term263 _88266 x y z).
Proof. exact (@lem3399354 (term264 _88266 y x z) (y = z)). Qed.
Lemma lem3399357 (a : Prop) (b : Prop) : (term265 a b) = (term266 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3399358 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term267 _88266 y x z) = (term268 _88266 y x z).
Proof. exact (@lem3399357 (term256 _88266 x y) (term256 _88266 x z)). Qed.
Lemma lem3399360 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3399361 {_88266 : Type'} (x : _88266) (y : _88266) : (term269 _88266 x y) = (x = y).
Proof. exact (@lem3399360 (x = y)). Qed.
Lemma lem3399362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3399363 {_88266 : Type'} (x : _88266) (y : _88266) : (term270 _88266 x y) = (term271 _88266 x y).
Proof. exact (MK_COMB (@lem3399362) (@lem3399361 _88266 x y)). Qed.
Lemma lem3399365 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3399366 {_88266 : Type'} (x : _88266) (z : _88266) : (term269 _88266 x z) = (x = z).
Proof. exact (@lem3399365 (x = z)). Qed.
Lemma lem3399367 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term268 _88266 y x z) = (term272 _88266 y x z).
Proof. exact (MK_COMB (@lem3399363 _88266 x y) (@lem3399366 _88266 x z)). Qed.
Lemma lem3399368 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term267 _88266 y x z) = (term272 _88266 y x z).
Proof. exact (TRANS (@lem3399358 _88266 y x z) (@lem3399367 _88266 y x z)). Qed.
Lemma lem3399369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3399370 {_88266 : Type'} (y : _88266) (x : _88266) (z : _88266) : (term273 _88266 y x z) = (term274 _88266 y x z).
Proof. exact (MK_COMB (@lem3399369) (@lem3399368 _88266 y x z)). Qed.
Lemma lem3399371 {_88266 : Type'} (y : _88266) (z : _88266) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3399372 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : (term263 _88266 x y z) = (term275 _88266 x y z).
Proof. exact (MK_COMB (@lem3399370 _88266 y x z) (@lem3399371 _88266 y z)). Qed.
Lemma lem3399373 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : (term260 _88266 y x z) = (term275 _88266 x y z).
Proof. exact (TRANS (@lem3399355 _88266 x y z) (@lem3399372 _88266 x y z)). Qed.
Lemma lem3399375 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term276 _88266 _88270 f x'' x.
Proof. exact (conj (@lem3399253 _88266 _88270 x'' f s t x h1 h2) (@lem3399262 _88266 _88270 f x'' x)). Qed.
Lemma lem3399377 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : term275 _88266 x y z.
Proof. exact (EQ_MP (@lem3399373 _88266 x y z) (@lem3399352 _88266 y x z)). Qed.
Lemma lem3399378 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : term275 _88266 x y z.
Proof. exact (@lem3399377 _88266 x y z). Qed.
Lemma lem3399379 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : term277 _88266 _88270 f x'' x.
Proof. exact (@lem3399378 _88266 (term245 _88266 _88270 f x'' x) x (term245 _88266 _88270 f x'' x)). Qed.
Lemma lem3399382 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : x = (term245 _88266 _88270 f x'' x).
Proof. exact (@lem3399379 _88266 _88270 f x'' x (@lem3399375 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399383 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term278 _88266 _88270 f x'' x.
Proof. exact (fun h0 : term279 _88266 _88270 f x'' x => @lem3399382 _88266 _88270 x'' f s t x h1 h2). Qed.
Lemma lem3399385 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399386 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term278 _88266 _88270 f x'' x) = (x = (term245 _88266 _88270 f x'' x)).
Proof. exact (@lem3399385 (x = (term245 _88266 _88270 f x'' x))). Qed.
Lemma lem3399387 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : x = (term245 _88266 _88270 f x'' x).
Proof. exact (EQ_MP (@lem3399386 _88266 _88270 f x'' x) (@lem3399383 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399389 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : t x.
Proof. exact (proj2 (@lem3398787 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399390 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term227 _88266 t x.
Proof. exact (fun h0 : term109 _88266 t x => @lem3399389 _88266 _88270 f s t x h1). Qed.
Lemma lem3399392 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399393 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term227 _88266 t x) = (t x).
Proof. exact (@lem3399392 (t x)). Qed.
Lemma lem3399394 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : t x.
Proof. exact (EQ_MP (@lem3399393 _88266 t x) (@lem3399390 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399396 {_88266 _88270 : Type'} (_35806 : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term249 _88266 _88270 t f x'' _35806.
Proof. exact (EQ_MP (@lem3399240 _88266 _88270 t f x'' _35806) (@lem3399229 _88266 _88270 _35806 x'' t f s h1)). Qed.
Lemma lem3399397 {_88266 _88270 : Type'} (_35806 : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term249 _88266 _88270 t f x'' _35806.
Proof. exact (@lem3399396 _88266 _88270 _35806 x'' t f s h1). Qed.
Lemma lem3399398 {_88266 _88270 : Type'} (x : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term249 _88266 _88270 t f x'' x.
Proof. exact (@lem3399397 _88266 _88270 x x'' t f s h1). Qed.
Lemma lem3399401 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : (term245 _88266 _88270 f x'' x) = x.
Proof. exact (@lem3399398 _88266 _88270 x x'' t f s h1 (@lem3399394 _88266 _88270 f s t x h2)). Qed.
Lemma lem3399402 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term250 _88266 _88270 f x'' x.
Proof. exact (fun h0 : term251 _88266 _88270 f x'' x => @lem3399401 _88266 _88270 x'' f s t x h1 h2). Qed.
Lemma lem3399404 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399405 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term250 _88266 _88270 f x'' x) = ((term245 _88266 _88270 f x'' x) = x).
Proof. exact (@lem3399404 ((term245 _88266 _88270 f x'' x) = x)). Qed.
Lemma lem3399406 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : (term245 _88266 _88270 f x'' x) = x.
Proof. exact (EQ_MP (@lem3399405 _88266 _88270 f x'' x) (@lem3399402 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399408 {_88266 : Type'} (x : _88266) : x = x.
Proof. exact (@lem21386 _88266 x). Qed.
Lemma lem3399409 {_88266 : Type'} (x : _88266) : x = x.
Proof. exact (@lem3399408 _88266 x). Qed.
Lemma lem3399410 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x).
Proof. exact (@lem3399409 _88266 (term245 _88266 _88270 f x'' x)). Qed.
Lemma lem3399411 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : term252 _88266 _88270 f x'' x.
Proof. exact (fun h0 : term253 _88266 _88270 f x'' x => @lem3399410 _88266 _88270 f x'' x). Qed.
Lemma lem3399413 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399414 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term252 _88266 _88270 f x'' x) = ((term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x)).
Proof. exact (@lem3399413 ((term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x))). Qed.
Lemma lem3399415 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term245 _88266 _88270 f x'' x) = (term245 _88266 _88270 f x'' x).
Proof. exact (EQ_MP (@lem3399414 _88266 _88270 f x'' x) (@lem3399411 _88266 _88270 f x'' x)). Qed.
Lemma lem3399416 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term276 _88266 _88270 f x'' x.
Proof. exact (conj (@lem3399406 _88266 _88270 x'' f s t x h1 h2) (@lem3399415 _88266 _88270 f x'' x)). Qed.
Lemma lem3399418 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : term275 _88266 x y z.
Proof. exact (EQ_MP (@lem3399373 _88266 x y z) (@lem3399352 _88266 y x z)). Qed.
Lemma lem3399419 {_88266 : Type'} (x : _88266) (y : _88266) (z : _88266) : term275 _88266 x y z.
Proof. exact (@lem3399418 _88266 x y z). Qed.
Lemma lem3399420 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : term277 _88266 _88270 f x'' x.
Proof. exact (@lem3399419 _88266 (term245 _88266 _88270 f x'' x) x (term245 _88266 _88270 f x'' x)). Qed.
Lemma lem3399423 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : x = (term245 _88266 _88270 f x'' x).
Proof. exact (@lem3399420 _88266 _88270 f x'' x (@lem3399416 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399424 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term278 _88266 _88270 f x'' x.
Proof. exact (fun h0 : term279 _88266 _88270 f x'' x => @lem3399423 _88266 _88270 x'' f s t x h1 h2). Qed.
Lemma lem3399426 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399427 {_88266 _88270 : Type'} (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term278 _88266 _88270 f x'' x) = (x = (term245 _88266 _88270 f x'' x)).
Proof. exact (@lem3399426 (x = (term245 _88266 _88270 f x'' x))). Qed.
Lemma lem3399428 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : x = (term245 _88266 _88270 f x'' x).
Proof. exact (EQ_MP (@lem3399427 _88266 _88270 f x'' x) (@lem3399424 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399430 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : t x.
Proof. exact (proj2 (@lem3398787 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399431 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term227 _88266 t x.
Proof. exact (fun h0 : term109 _88266 t x => @lem3399430 _88266 _88270 f s t x h1). Qed.
Lemma lem3399433 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399434 {_88266 : Type'} (t : _88266 -> Prop) (x : _88266) : (term227 _88266 t x) = (t x).
Proof. exact (@lem3399433 (t x)). Qed.
Lemma lem3399435 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : t x.
Proof. exact (EQ_MP (@lem3399434 _88266 t x) (@lem3399431 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399441 (q : Prop) (p : Prop) (r : Prop) : (term259 p q r) = (term259 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3399442 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : (term242 _88266 _35833 t _35832) = (term280 _88266 _35833 t _35832).
Proof. exact (@lem3399441 (t _35833) (term256 _88266 _35832 _35833) (term109 _88266 t _35832)). Qed.
Lemma lem3399456 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3399457 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : (term281 _88266 _35833 t _35832) = (term282 _88266 t _35832 _35833).
Proof. exact (@lem3399456 (term109 _88266 t _35832) (term256 _88266 _35832 _35833)). Qed.
Lemma lem3399465 {_88266 : Type'} (t : _88266 -> Prop) (_35833 : _88266) : (term283 _88266 t _35833) = (term283 _88266 t _35833).
Proof. exact (eq_refl (term283 _88266 t _35833)). Qed.
Lemma lem3399466 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : (term280 _88266 _35833 t _35832) = (term284 _88266 t _35832 _35833).
Proof. exact (MK_COMB (@lem3399465 _88266 t _35833) (@lem3399457 _88266 t _35832 _35833)). Qed.
Lemma lem3399477 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : (term242 _88266 _35833 t _35832) = (term284 _88266 t _35832 _35833).
Proof. exact (TRANS (@lem3399442 _88266 _35833 t _35832) (@lem3399466 _88266 t _35832 _35833)). Qed.
Lemma lem3399478 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399479 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : (term285 _88266 _35833 t _35832) = (term286 _88266 t _35832 _35833).
Proof. exact (MK_COMB (@lem3399478) (@lem3399477 _88266 t _35832 _35833)). Qed.
Lemma lem3399493 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3399494 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : (term281 _88266 _35833 t _35832) = (term282 _88266 t _35832 _35833).
Proof. exact (@lem3399493 (term109 _88266 t _35832) (term256 _88266 _35832 _35833)). Qed.
Lemma lem3399502 {_88266 : Type'} (t : _88266 -> Prop) (_35833 : _88266) : (term283 _88266 t _35833) = (term283 _88266 t _35833).
Proof. exact (eq_refl (term283 _88266 t _35833)). Qed.
Lemma lem3399503 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : (term280 _88266 _35833 t _35832) = (term284 _88266 t _35832 _35833).
Proof. exact (MK_COMB (@lem3399502 _88266 t _35833) (@lem3399494 _88266 t _35832 _35833)). Qed.
Lemma lem3399514 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : ((term242 _88266 _35833 t _35832) = (term280 _88266 _35833 t _35832)) = ((term284 _88266 t _35832 _35833) = (term284 _88266 t _35832 _35833)).
Proof. exact (MK_COMB (@lem3399479 _88266 t _35832 _35833) (@lem3399503 _88266 t _35832 _35833)). Qed.
Lemma lem3399516 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3399517 (x : Prop) : (x = x) = True.
Proof. exact (@lem3399516 Prop x). Qed.
Lemma lem3399518 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) (_35833 : _88266) : ((term284 _88266 t _35832 _35833) = (term284 _88266 t _35832 _35833)) = True.
Proof. exact (@lem3399517 (term284 _88266 t _35832 _35833)). Qed.
Lemma lem3399519 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : ((term242 _88266 _35833 t _35832) = (term280 _88266 _35833 t _35832)) = True.
Proof. exact (TRANS (@lem3399514 _88266 t _35832 _35833) (@lem3399518 _88266 t _35832 _35833)). Qed.
Lemma lem3399520 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : True = ((term242 _88266 _35833 t _35832) = (term280 _88266 _35833 t _35832)).
Proof. exact (SYM (@lem3399519 _88266 _35833 t _35832)). Qed.
Lemma lem3399521 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : (term242 _88266 _35833 t _35832) = (term280 _88266 _35833 t _35832).
Proof. exact (EQ_MP (@lem3399520 _88266 _35833 t _35832) (@lem0)). Qed.
Lemma lem3399522 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : term280 _88266 _35833 t _35832.
Proof. exact (EQ_MP (@lem3399521 _88266 _35833 t _35832) (@lem3399169 _88266 _35833 t _35832)). Qed.
Lemma lem3399524 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3399525 {_88266 : Type'} (_35832 : _88266) (t : _88266 -> Prop) (_35833 : _88266) : (term280 _88266 _35833 t _35832) = (term287 _88266 _35832 t _35833).
Proof. exact (@lem3399524 (term281 _88266 _35833 t _35832) (t _35833)). Qed.
Lemma lem3399527 (a : Prop) (b : Prop) : (term265 a b) = (term266 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3399528 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : (term288 _88266 _35833 t _35832) = (term289 _88266 _35833 t _35832).
Proof. exact (@lem3399527 (term256 _88266 _35832 _35833) (term109 _88266 t _35832)). Qed.
Lemma lem3399530 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3399531 {_88266 : Type'} (_35832 : _88266) (_35833 : _88266) : (term269 _88266 _35832 _35833) = (_35832 = _35833).
Proof. exact (@lem3399530 (_35832 = _35833)). Qed.
Lemma lem3399532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3399533 {_88266 : Type'} (_35832 : _88266) (_35833 : _88266) : (term270 _88266 _35832 _35833) = (term271 _88266 _35832 _35833).
Proof. exact (MK_COMB (@lem3399532) (@lem3399531 _88266 _35832 _35833)). Qed.
Lemma lem3399535 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3399536 {_88266 : Type'} (t : _88266 -> Prop) (_35832 : _88266) : (term231 _88266 t _35832) = (t _35832).
Proof. exact (@lem3399535 (t _35832)). Qed.
Lemma lem3399537 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : (term289 _88266 _35833 t _35832) = (term290 _88266 _35833 t _35832).
Proof. exact (MK_COMB (@lem3399533 _88266 _35832 _35833) (@lem3399536 _88266 t _35832)). Qed.
Lemma lem3399538 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : (term288 _88266 _35833 t _35832) = (term290 _88266 _35833 t _35832).
Proof. exact (TRANS (@lem3399528 _88266 _35833 t _35832) (@lem3399537 _88266 _35833 t _35832)). Qed.
Lemma lem3399539 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3399540 {_88266 : Type'} (_35833 : _88266) (t : _88266 -> Prop) (_35832 : _88266) : (term291 _88266 _35833 t _35832) = (term292 _88266 _35833 t _35832).
Proof. exact (MK_COMB (@lem3399539) (@lem3399538 _88266 _35833 t _35832)). Qed.
Lemma lem3399541 {_88266 : Type'} (t : _88266 -> Prop) (_35833 : _88266) : (t _35833) = (t _35833).
Proof. exact (eq_refl (t _35833)). Qed.
Lemma lem3399542 {_88266 : Type'} (_35832 : _88266) (t : _88266 -> Prop) (_35833 : _88266) : (term287 _88266 _35832 t _35833) = (term293 _88266 _35832 t _35833).
Proof. exact (MK_COMB (@lem3399540 _88266 _35833 t _35832) (@lem3399541 _88266 t _35833)). Qed.
Lemma lem3399543 {_88266 : Type'} (_35832 : _88266) (t : _88266 -> Prop) (_35833 : _88266) : (term280 _88266 _35833 t _35832) = (term293 _88266 _35832 t _35833).
Proof. exact (TRANS (@lem3399525 _88266 _35832 t _35833) (@lem3399542 _88266 _35832 t _35833)). Qed.
Lemma lem3399545 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term294 _88266 _88270 f x'' t x.
Proof. exact (conj (@lem3399428 _88266 _88270 x'' f s t x h1 h2) (@lem3399435 _88266 _88270 f s t x h2)). Qed.
Lemma lem3399547 {_88266 : Type'} (_35832 : _88266) (t : _88266 -> Prop) (_35833 : _88266) : term293 _88266 _35832 t _35833.
Proof. exact (EQ_MP (@lem3399543 _88266 _35832 t _35833) (@lem3399522 _88266 _35833 t _35832)). Qed.
Lemma lem3399548 {_88266 : Type'} (_35832 : _88266) (t : _88266 -> Prop) (_35833 : _88266) : term293 _88266 _35832 t _35833.
Proof. exact (@lem3399547 _88266 _35832 t _35833). Qed.
Lemma lem3399549 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : term295 _88266 _88270 t f x'' x.
Proof. exact (@lem3399548 _88266 x t (term245 _88266 _88270 f x'' x)). Qed.
Lemma lem3399552 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term296 _88266 _88270 t f x'' x.
Proof. exact (@lem3399549 _88266 _88270 t f x'' x (@lem3399545 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399553 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term297 _88266 _88270 t f x'' x.
Proof. exact (fun h0 : term298 _88266 _88270 t f x'' x => @lem3399552 _88266 _88270 x'' f s t x h1 h2). Qed.
Lemma lem3399555 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399556 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (x'' : _88266 -> _88270) (x : _88266) : (term297 _88266 _88270 t f x'' x) = (term296 _88266 _88270 t f x'' x).
Proof. exact (@lem3399555 (term296 _88266 _88270 t f x'' x)). Qed.
Lemma lem3399557 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term296 _88266 _88270 t f x'' x.
Proof. exact (EQ_MP (@lem3399556 _88266 _88270 t f x'' x) (@lem3399553 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399563 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3399564 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : (term90 _88266 _88270 t f s _35808) = (term299 _88266 _88270 s t f _35808).
Proof. exact (@lem3399563 (s _35808) (term224 _88266 _88270 t f _35808)). Qed.
Lemma lem3399570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3399571 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : (term300 _88266 _88270 t f s _35808) = (term301 _88266 _88270 s t f _35808).
Proof. exact (MK_COMB (@lem3399570) (@lem3399564 _88266 _88270 s t f _35808)). Qed.
Lemma lem3399577 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : (term299 _88266 _88270 s t f _35808) = (term299 _88266 _88270 s t f _35808).
Proof. exact (eq_refl (term299 _88266 _88270 s t f _35808)). Qed.
Lemma lem3399578 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : ((term90 _88266 _88270 t f s _35808) = (term299 _88266 _88270 s t f _35808)) = ((term299 _88266 _88270 s t f _35808) = (term299 _88266 _88270 s t f _35808)).
Proof. exact (MK_COMB (@lem3399571 _88266 _88270 s t f _35808) (@lem3399577 _88266 _88270 s t f _35808)). Qed.
Lemma lem3399580 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3399581 (x : Prop) : (x = x) = True.
Proof. exact (@lem3399580 Prop x). Qed.
Lemma lem3399582 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : ((term299 _88266 _88270 s t f _35808) = (term299 _88266 _88270 s t f _35808)) = True.
Proof. exact (@lem3399581 (term299 _88266 _88270 s t f _35808)). Qed.
Lemma lem3399583 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : ((term90 _88266 _88270 t f s _35808) = (term299 _88266 _88270 s t f _35808)) = True.
Proof. exact (TRANS (@lem3399578 _88266 _88270 s t f _35808) (@lem3399582 _88266 _88270 s t f _35808)). Qed.
Lemma lem3399584 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : True = ((term90 _88266 _88270 t f s _35808) = (term299 _88266 _88270 s t f _35808)).
Proof. exact (SYM (@lem3399583 _88266 _88270 s t f _35808)). Qed.
Lemma lem3399585 {_88266 _88270 : Type'} (s : _88270 -> Prop) (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : (term90 _88266 _88270 t f s _35808) = (term299 _88266 _88270 s t f _35808).
Proof. exact (EQ_MP (@lem3399584 _88266 _88270 s t f _35808) (@lem0)). Qed.
Lemma lem3399586 {_88266 _88270 : Type'} (_35808 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term299 _88266 _88270 s t f _35808.
Proof. exact (EQ_MP (@lem3399585 _88266 _88270 s t f _35808) (@lem3398963 _88266 _88270 _35808 x'' t f s h1)). Qed.
Lemma lem3399588 (b : Prop) (a : Prop) : (a \/ b) = (term229 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3399589 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35808 : _88270) : (term299 _88266 _88270 s t f _35808) = (term302 _88266 _88270 t f s _35808).
Proof. exact (@lem3399588 (term224 _88266 _88270 t f _35808) (s _35808)). Qed.
Lemma lem3399591 (a : Prop) : (term62 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3399592 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : (term303 _88266 _88270 t f _35808) = (term25 _88266 _88270 t f _35808).
Proof. exact (@lem3399591 (term25 _88266 _88270 t f _35808)). Qed.
Lemma lem3399593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3399594 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (_35808 : _88270) : (term304 _88266 _88270 t f _35808) = (term305 _88266 _88270 t f _35808).
Proof. exact (MK_COMB (@lem3399593) (@lem3399592 _88266 _88270 t f _35808)). Qed.
Lemma lem3399595 {_88270 : Type'} (s : _88270 -> Prop) (_35808 : _88270) : (s _35808) = (s _35808).
Proof. exact (eq_refl (s _35808)). Qed.
Lemma lem3399596 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35808 : _88270) : (term302 _88266 _88270 t f s _35808) = (term306 _88266 _88270 t f s _35808).
Proof. exact (MK_COMB (@lem3399594 _88266 _88270 t f _35808) (@lem3399595 _88270 s _35808)). Qed.
Lemma lem3399597 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35808 : _88270) : (term299 _88266 _88270 s t f _35808) = (term306 _88266 _88270 t f s _35808).
Proof. exact (TRANS (@lem3399589 _88266 _88270 t f s _35808) (@lem3399596 _88266 _88270 t f s _35808)). Qed.
Lemma lem3399600 {_88266 _88270 : Type'} (_35808 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term306 _88266 _88270 t f s _35808.
Proof. exact (EQ_MP (@lem3399597 _88266 _88270 t f s _35808) (@lem3399586 _88266 _88270 _35808 x'' t f s h1)). Qed.
Lemma lem3399601 {_88266 _88270 : Type'} (_35808 : _88270) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term306 _88266 _88270 t f s _35808.
Proof. exact (@lem3399600 _88266 _88270 _35808 x'' t f s h1). Qed.
Lemma lem3399602 {_88266 _88270 : Type'} (x : _88266) (x'' : _88266 -> _88270) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term162 _88266 _88270 x'' t f s) : term307 _88266 _88270 t f s x'' x.
Proof. exact (@lem3399601 _88266 _88270 (x'' x) x'' t f s h1). Qed.
Lemma lem3399605 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term308 _88266 _88270 s x'' x.
Proof. exact (@lem3399602 _88266 _88270 x x'' t f s h1 (@lem3399557 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399606 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term309 _88266 _88270 s x'' x.
Proof. exact (fun h0 : term310 _88266 _88270 s x'' x => @lem3399605 _88266 _88270 x'' f s t x h1 h2). Qed.
Lemma lem3399608 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399609 {_88266 _88270 : Type'} (s : _88270 -> Prop) (x'' : _88266 -> _88270) (x : _88266) : (term309 _88266 _88270 s x'' x) = (term308 _88266 _88270 s x'' x).
Proof. exact (@lem3399608 (term308 _88266 _88270 s x'' x)). Qed.
Lemma lem3399610 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term308 _88266 _88270 s x'' x.
Proof. exact (EQ_MP (@lem3399609 _88266 _88270 s x'' x) (@lem3399606 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399612 (a : Prop) (b : Prop) : (term311 a b) = (term312 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3399613 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35809 : _88270) : (term167 _88266 _88270 x f s _35809) = (term166 _88266 _88270 x f s _35809).
Proof. exact (@lem3399612 (x = (f _35809)) (s _35809)). Qed.
Lemma lem3399615 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3399616 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35809 : _88270) : (term166 _88266 _88270 x f s _35809) = (term313 _88266 _88270 x f s _35809).
Proof. exact (@lem3399615 (term41 _88266 _88270 x f s _35809)). Qed.
Lemma lem3399617 {_88266 _88270 : Type'} (x : _88266) (f : _88270 -> _88266) (s : _88270 -> Prop) (_35809 : _88270) : (term167 _88266 _88270 x f s _35809) = (term313 _88266 _88270 x f s _35809).
Proof. exact (TRANS (@lem3399613 _88266 _88270 x f s _35809) (@lem3399616 _88266 _88270 x f s _35809)). Qed.
Lemma lem3399619 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term314 _88266 _88270 f s x'' x.
Proof. exact (conj (@lem3399387 _88266 _88270 x'' f s t x h1 h2) (@lem3399610 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399621 {_88266 _88270 : Type'} (_35809 : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term313 _88266 _88270 x f s _35809.
Proof. exact (EQ_MP (@lem3399617 _88266 _88270 x f s _35809) (@lem3398969 _88266 _88270 _35809 f s t x h1)). Qed.
Lemma lem3399622 {_88266 _88270 : Type'} (_35809 : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term313 _88266 _88270 x f s _35809.
Proof. exact (@lem3399621 _88266 _88270 _35809 f s t x h1). Qed.
Lemma lem3399623 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term180 _88266 _88270 f s t x) : term315 _88266 _88270 f s x'' x.
Proof. exact (@lem3399622 _88266 _88270 (x'' x) f s t x h1). Qed.
Lemma lem3399626 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : False.
Proof. exact (@lem3399623 _88266 _88270 x'' f s t x h2 (@lem3399619 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399627 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : term236.
Proof. exact (fun h0 : ~ False => @lem3399626 _88266 _88270 x'' f s t x h1 h2). Qed.
Lemma lem3399629 (p : Prop) : (term228 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3399630 : term236 = False.
Proof. exact (@lem3399629 False). Qed.
Lemma lem3399631 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term180 _88266 _88270 f s t x) : False.
Proof. exact (EQ_MP (@lem3399630) (@lem3399627 _88266 _88270 x'' f s t x h1 h2)). Qed.
Lemma lem3399632 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (x' : _88270) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term196 _88266 _88270 f s x' t x) : False.
Proof. exact (EQ_MP (@lem3399144) (@lem3399141 _88266 _88270 x'' f s x' t x h1 h2)). Qed.
Lemma lem3399633 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term215 _88266 _88270 x' f s t x) : False.
Proof. exact (or_elim (@lem3398722 _88266 _88270 x' f s t x h2) (fun h0 : term196 _88266 _88270 f s x' t x => @lem3399632 _88266 _88270 x'' f s x' t x h1 h0) (fun h0 : term180 _88266 _88270 f s t x => @lem3399631 _88266 _88270 x'' f s t x h1 h0)). Qed.
Lemma lem3399634 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term215 _88266 _88270 x' f s t x) : (term162 _88266 _88270 x'' t f s) = False.
Proof. exact (prop_ext (fun h3 : term162 _88266 _88270 x'' t f s => @lem3399633 _88266 _88270 x'' x' f s t x h1 h2) (fun h3 : False => @lem3398781 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3399635 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term215 _88266 _88270 x' f s t x) : False.
Proof. exact (EQ_MP (@lem3399634 _88266 _88270 x'' x' f s t x h1 h2) (@lem3398781 _88266 _88270 x'' t f s h1)). Qed.
Lemma lem3399636 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term215 _88266 _88270 x' f s t x) : (term215 _88266 _88270 x' f s t x) = False.
Proof. exact (prop_ext (fun h3 : term215 _88266 _88270 x' f s t x => @lem3399635 _88266 _88270 x'' x' f s t x h1 h2) (fun h3 : False => @lem3398722 _88266 _88270 x' f s t x h2)). Qed.
Lemma lem3399637 {_88266 _88270 : Type'} (x'' : _88266 -> _88270) (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term162 _88266 _88270 x'' t f s) (h2 : term215 _88266 _88270 x' f s t x) : False.
Proof. exact (EQ_MP (@lem3399636 _88266 _88270 x'' x' f s t x h1 h2) (@lem3398722 _88266 _88270 x' f s t x h2)). Qed.
Lemma lem3399638 {_88266 _88270 : Type'} (x' : _88270) (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) (x : _88266) (h1 : term33 _88266 _88270 t f s) (h2 : term215 _88266 _88270 x' f s t x) : False.
Proof. exact (ex_elim (@lem3398494 _88266 _88270 t f s h1) (fun x'' : _88266 -> _88270 => fun h0 : term164 _88266 _88270 t f s x'' => @lem3399637 _88266 _88270 x'' x' f s t x h0 h2)). Qed.
Lemma lem3399639 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term69 _88266 _88270 f s t x) (h2 : term33 _88266 _88270 t f s) : False.
Proof. exact (ex_elim (@lem3398669 _88266 _88270 f s t x h1) (fun x' : _88270 => fun h0 : term217 _88266 _88270 f s t x x' => @lem3399638 _88266 _88270 x' f s t x h2 h0)). Qed.
Lemma lem3399640 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term69 _88266 _88270 f s t x) (h2 : term33 _88266 _88270 t f s) : (term69 _88266 _88270 f s t x) = False.
Proof. exact (prop_ext (fun h3 : term69 _88266 _88270 f s t x => @lem3399639 _88266 _88270 x t f s h1 h2) (fun h3 : False => @lem3398213 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399641 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term69 _88266 _88270 f s t x) (h2 : term33 _88266 _88270 t f s) : False.
Proof. exact (EQ_MP (@lem3399640 _88266 _88270 x t f s h1 h2) (@lem3398213 _88266 _88270 f s t x h1)). Qed.
Lemma lem3399642 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term33 _88266 _88270 t f s) : term68 _88266 _88270 f s t x.
Proof. exact (fun h0 : term69 _88266 _88270 f s t x => @lem3399641 _88266 _88270 x t f s h0 h1). Qed.
Lemma lem3399643 {_88266 _88270 : Type'} (x : _88266) (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term33 _88266 _88270 t f s) : (term44 _88266 _88270 x f s) = (t x).
Proof. exact (EQ_MP (@lem3398212 _88266 _88270 f s t x) (@lem3399642 _88266 _88270 x t f s h1)). Qed.
Lemma lem3399648 {_88266 _88270 : Type'} (t : _88266 -> Prop) (f : _88270 -> _88266) (s : _88270 -> Prop) (h1 : term33 _88266 _88270 t f s) : term49 _88266 _88270 f s t.
Proof. exact (fun x : _88266 => @lem3399643 _88266 _88270 x t f s h1). Qed.
Lemma lem3399649 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : term50 _88266 _88270 f s t.
Proof. exact (fun h0 : term33 _88266 _88270 t f s => @lem3399648 _88266 _88270 t f s h0). Qed.
Lemma lem3399654 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) : term52 _88266 _88270 f s.
Proof. exact (fun t : _88266 -> Prop => @lem3399649 _88266 _88270 f s t). Qed.
Lemma lem3399659 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term54 _88266 _88270 f.
Proof. exact (fun s : _88270 -> Prop => @lem3399654 _88266 _88270 f s). Qed.
Lemma lem3399664 {_88266 _88270 : Type'} : term66 _88266 _88270.
Proof. exact (fun f : _88270 -> _88266 => @lem3399659 _88266 _88270 f). Qed.
Lemma lem3399665 {_88266 _88270 : Type'} : term65 _88266 _88270.
Proof. exact (EQ_MP (@lem3398207 _88266 _88270) (@lem3399664 _88266 _88270)). Qed.
Lemma lem3399666 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term316 _88266 _88270 f.
Proof. exact (@lem3399665 _88266 _88270 f). Qed.
Lemma lem3399667 {_88266 _88270 : Type'} (f : _88270 -> _88266) : (term316 _88266 _88270 f) = (term56 _88266 _88270 f).
Proof. exact (eq_refl (term316 _88266 _88270 f)). Qed.
Lemma lem3399668 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term56 _88266 _88270 f.
Proof. exact (EQ_MP (@lem3399667 _88266 _88270 f) (@lem3399666 _88266 _88270 f)). Qed.
Lemma lem3399670 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term56 _88266 _88270 f.
Proof. exact (@lem3398012 _88266 _88270 f (@lem3399668 _88266 _88270 f)). Qed.
Lemma lem3399671 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term57 _88266 _88270 f) : False.
Proof. exact (@lem3399670 _88266 _88270 f (@lem3397996 _88266 _88270 f h1)). Qed.
Lemma lem3399672 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term57 _88266 _88270 f) : (term57 _88266 _88270 f) = False.
Proof. exact (prop_ext (fun h2 : term57 _88266 _88270 f => @lem3399671 _88266 _88270 f h1) (fun h2 : False => @lem3397996 _88266 _88270 f h1)). Qed.
Lemma lem3399673 {_88266 _88270 : Type'} (f : _88270 -> _88266) (h1 : term57 _88266 _88270 f) : False.
Proof. exact (EQ_MP (@lem3399672 _88266 _88270 f h1) (@lem3397996 _88266 _88270 f h1)). Qed.
Lemma lem3399674 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term56 _88266 _88270 f.
Proof. exact (fun h0 : term57 _88266 _88270 f => @lem3399673 _88266 _88270 f h0). Qed.
Lemma lem3399675 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term54 _88266 _88270 f.
Proof. exact (EQ_MP (@lem3397995 _88266 _88270 f) (@lem3399674 _88266 _88270 f)). Qed.
Lemma lem3399676 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term12 _88266 _88270 f.
Proof. exact (EQ_MP (@lem3397991 _88266 _88270 f) (@lem3399675 _88266 _88270 f)). Qed.
Lemma lem3399677 {_88266 _88270 : Type'} (f : _88270 -> _88266) : term11 _88266 _88270 f.
Proof. exact (EQ_MP (@lem3397849 _88266 _88270 f) (@lem3399676 _88266 _88270 f)). Qed.
