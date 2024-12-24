Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SIMPLE_IMAGE_GEN_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
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
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211647_spec.
Require Import thm3211648_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3394015 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3394016 {_88162 : Type'} (s : _88162 -> Prop) (t : _88162 -> Prop) : (s = t) = (term0 _88162 s t).
Proof. exact (@lem3394015 _88162 s t). Qed.
Lemma lem3394017 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : ((term1 _88162 _88175 P f) = (term2 _88162 _88175 f P)) = (term3 _88162 _88175 f P).
Proof. exact (@lem3394016 _88162 (term1 _88162 _88175 P f) (term2 _88162 _88175 f P)). Qed.
Lemma lem3394034 {_88162 _88175 : Type'} (f : _88175 -> _88162) : (term4 _88162 _88175 f) = (term5 _88162 _88175 f).
Proof. exact (fun_ext (fun P : _88175 -> Prop => @lem3394017 _88162 _88175 f P)). Qed.
Lemma lem3394035 {_88175 : Type'} : (@all (_88175 -> Prop)) = (@all (_88175 -> Prop)).
Proof. exact (eq_refl (@all (_88175 -> Prop))). Qed.
Lemma lem3394036 {_88162 _88175 : Type'} (f : _88175 -> _88162) : (term6 _88162 _88175 f) = (term7 _88162 _88175 f).
Proof. exact (MK_COMB (@lem3394035 _88175) (@lem3394034 _88162 _88175 f)). Qed.
Lemma lem3394041 {_88162 _88175 : Type'} : (term8 _88162 _88175) = (term9 _88162 _88175).
Proof. exact (fun_ext (fun f : _88175 -> _88162 => @lem3394036 _88162 _88175 f)). Qed.
Lemma lem3394042 {_88162 _88175 : Type'} : (@all (_88175 -> _88162)) = (@all (_88175 -> _88162)).
Proof. exact (eq_refl (@all (_88175 -> _88162))). Qed.
Lemma lem3394043 {_88162 _88175 : Type'} : (term10 _88162 _88175) = (term11 _88162 _88175).
Proof. exact (MK_COMB (@lem3394042 _88162 _88175) (@lem3394041 _88162 _88175)). Qed.
Lemma lem3394048 {_88162 _88175 : Type'} : (term11 _88162 _88175) = (term10 _88162 _88175).
Proof. exact (SYM (@lem3394043 _88162 _88175)). Qed.
Lemma lem3394066 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term12 _83064 x P) = (term13 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem3394067 {_88162 : Type'} (P : type919 _88162) (x : _88162) : (term12 _88162 x P) = (term13 _88162 P x).
Proof. exact (@lem3394066 _88162 P x). Qed.
Lemma lem3394068 {_88162 _88175 : Type'} (P : _88175 -> Prop) (f : _88175 -> _88162) (x : _88162) : (term14 _88162 _88175 x P f) = (term15 _88162 _88175 P f x).
Proof. exact (@lem3394067 _88162 (term16 _88162 _88175 P f) x). Qed.
Lemma lem3394069 {_88162 _88175 : Type'} (GEN_PVAR_24 : _88162) (P : _88175 -> Prop) (f : _88175 -> _88162) : (term17 _88162 _88175 P f GEN_PVAR_24) = (term18 _88162 _88175 GEN_PVAR_24 P f).
Proof. exact (eq_refl (term17 _88162 _88175 P f GEN_PVAR_24)). Qed.
Lemma lem3394070 {_88162 _88175 : Type'} (P : _88175 -> Prop) (f : _88175 -> _88162) : (term19 _88162 _88175 P f) = (term20 _88162 _88175 P f).
Proof. exact (fun_ext (fun GEN_PVAR_24 : _88162 => @lem3394069 _88162 _88175 GEN_PVAR_24 P f)). Qed.
Lemma lem3394071 {_88162 : Type'} : (@GSPEC _88162) = (@GSPEC _88162).
Proof. exact (eq_refl (@GSPEC _88162)). Qed.
Lemma lem3394072 {_88162 _88175 : Type'} (P : _88175 -> Prop) (f : _88175 -> _88162) : (term21 _88162 _88175 P f) = (term1 _88162 _88175 P f).
Proof. exact (MK_COMB (@lem3394071 _88162) (@lem3394070 _88162 _88175 P f)). Qed.
Lemma lem3394073 {_88162 : Type'} (x : _88162) : (@IN _88162 x) = (@IN _88162 x).
Proof. exact (eq_refl (@IN _88162 x)). Qed.
Lemma lem3394074 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (f : _88175 -> _88162) : (term14 _88162 _88175 x P f) = (term22 _88162 _88175 x P f).
Proof. exact (MK_COMB (@lem3394073 _88162 x) (@lem3394072 _88162 _88175 P f)). Qed.
Lemma lem3394075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394076 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (f : _88175 -> _88162) : (term23 _88162 _88175 x P f) = (term24 _88162 _88175 x P f).
Proof. exact (MK_COMB (@lem3394075) (@lem3394074 _88162 _88175 x P f)). Qed.
Lemma lem3394077 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (f : _88175 -> _88162) : (term15 _88162 _88175 P f x) = (term25 _88162 _88175 x P f).
Proof. exact (eq_refl (term15 _88162 _88175 P f x)). Qed.
Lemma lem3394078 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (f : _88175 -> _88162) : ((term14 _88162 _88175 x P f) = (term15 _88162 _88175 P f x)) = ((term22 _88162 _88175 x P f) = (term25 _88162 _88175 x P f)).
Proof. exact (MK_COMB (@lem3394076 _88162 _88175 x P f) (@lem3394077 _88162 _88175 x P f)). Qed.
Lemma lem3394079 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (f : _88175 -> _88162) : (term22 _88162 _88175 x P f) = (term25 _88162 _88175 x P f).
Proof. exact (EQ_MP (@lem3394078 _88162 _88175 x P f) (@lem3394068 _88162 _88175 P f x)). Qed.
Lemma lem3394085 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3394086 {_88162 : Type'} (f : type1538 _88162) (y : Prop) : (term27 _88162 f y) = (f y).
Proof. exact (@lem3394085 Prop (_88162 -> Prop) f y). Qed.
Lemma lem3394087 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (x' : _88175) : (term28 _88162 _88175 x P x') = (term29 _88162 _88175 x P x').
Proof. exact (@lem3394086 _88162 (term30 _88162 x) (P x')). Qed.
Lemma lem3394088 {_88162 : Type'} (p : Prop) (x : _88162) : (term31 _88162 x p) = (term32 _88162 p x).
Proof. exact (eq_refl (term31 _88162 x p)). Qed.
Lemma lem3394089 {_88162 : Type'} (x : _88162) : (term33 _88162 x) = (term30 _88162 x).
Proof. exact (fun_ext (fun p : Prop => @lem3394088 _88162 p x)). Qed.
Lemma lem3394090 {_88175 : Type'} (P : _88175 -> Prop) (x : _88175) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3394091 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (x' : _88175) : (term28 _88162 _88175 x P x') = (term29 _88162 _88175 x P x').
Proof. exact (MK_COMB (@lem3394089 _88162 x) (@lem3394090 _88175 P x')). Qed.
Lemma lem3394092 {_88162 : Type'} : (@eq (_88162 -> Prop)) = (@eq (_88162 -> Prop)).
Proof. exact (eq_refl (@eq (_88162 -> Prop))). Qed.
Lemma lem3394093 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (x' : _88175) : (term34 _88162 _88175 x P x') = (term35 _88162 _88175 x P x').
Proof. exact (MK_COMB (@lem3394092 _88162) (@lem3394091 _88162 _88175 x P x')). Qed.
Lemma lem3394094 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88175) (x' : _88162) : (term29 _88162 _88175 x' P x) = (term36 _88162 _88175 P x x').
Proof. exact (eq_refl (term29 _88162 _88175 x' P x)). Qed.
Lemma lem3394095 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88175) (x' : _88162) : ((term28 _88162 _88175 x' P x) = (term29 _88162 _88175 x' P x)) = ((term29 _88162 _88175 x' P x) = (term36 _88162 _88175 P x x')).
Proof. exact (MK_COMB (@lem3394093 _88162 _88175 x' P x) (@lem3394094 _88162 _88175 P x x')). Qed.
Lemma lem3394096 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88175) (x' : _88162) : (term29 _88162 _88175 x' P x) = (term36 _88162 _88175 P x x').
Proof. exact (EQ_MP (@lem3394095 _88162 _88175 P x x') (@lem3394087 _88162 _88175 x' P x)). Qed.
Lemma lem3394101 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x : _88175) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3394102 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term37 _88162 _88175 x P f x') = (term38 _88162 _88175 P x f x').
Proof. exact (MK_COMB (@lem3394096 _88162 _88175 P x' x) (@lem3394101 _88162 _88175 f x')). Qed.
Lemma lem3394104 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3394105 {_88162 : Type'} (f : _88162 -> Prop) (y : _88162) : (term39 _88162 f y) = (f y).
Proof. exact (@lem3394104 _88162 Prop f y). Qed.
Lemma lem3394106 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term40 _88162 _88175 P x f x') = (term38 _88162 _88175 P x f x').
Proof. exact (@lem3394105 _88162 (term36 _88162 _88175 P x' x) (f x')). Qed.
Lemma lem3394107 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88175) (x' : _88162) (t : _88162) : (term41 _88162 _88175 P x x' t) = (term42 _88162 _88175 P x x' t).
Proof. exact (eq_refl (term41 _88162 _88175 P x x' t)). Qed.
Lemma lem3394108 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88175) (x' : _88162) : (term43 _88162 _88175 P x x') = (term36 _88162 _88175 P x x').
Proof. exact (fun_ext (fun t : _88162 => @lem3394107 _88162 _88175 P x x' t)). Qed.
Lemma lem3394109 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x : _88175) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3394110 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term40 _88162 _88175 P x f x') = (term38 _88162 _88175 P x f x').
Proof. exact (MK_COMB (@lem3394108 _88162 _88175 P x' x) (@lem3394109 _88162 _88175 f x')). Qed.
Lemma lem3394111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394112 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term44 _88162 _88175 P x f x') = (term45 _88162 _88175 P x f x').
Proof. exact (MK_COMB (@lem3394111) (@lem3394110 _88162 _88175 P x f x')). Qed.
Lemma lem3394113 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term38 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x').
Proof. exact (eq_refl (term38 _88162 _88175 P x f x')). Qed.
Lemma lem3394114 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : ((term40 _88162 _88175 P x f x') = (term38 _88162 _88175 P x f x')) = ((term38 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x')).
Proof. exact (MK_COMB (@lem3394112 _88162 _88175 P x f x') (@lem3394113 _88162 _88175 P x f x')). Qed.
Lemma lem3394115 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term38 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x').
Proof. exact (EQ_MP (@lem3394114 _88162 _88175 P x f x') (@lem3394106 _88162 _88175 P x f x')). Qed.
Lemma lem3394120 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term37 _88162 _88175 x P f x') = (term46 _88162 _88175 P x f x').
Proof. exact (TRANS (@lem3394102 _88162 _88175 P x f x') (@lem3394115 _88162 _88175 P x f x')). Qed.
Lemma lem3394121 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term47 _88162 _88175 x P f) = (term48 _88162 _88175 P x f).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394120 _88162 _88175 P x f x')). Qed.
Lemma lem3394122 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394123 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term25 _88162 _88175 x P f) = (term49 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394122 _88175) (@lem3394121 _88162 _88175 P x f)). Qed.
Lemma lem3394128 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term22 _88162 _88175 x P f) = (term49 _88162 _88175 P x f).
Proof. exact (TRANS (@lem3394079 _88162 _88175 x P f) (@lem3394123 _88162 _88175 P x f)). Qed.
Lemma lem3394129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394130 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term24 _88162 _88175 x P f) = (term50 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394129) (@lem3394128 _88162 _88175 P x f)). Qed.
Lemma lem3394132 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term51 A B y f s) = (term52 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3394133 {_88162 _88175 : Type'} (y : _88162) (f : _88175 -> _88162) (s : _88175 -> Prop) : (term53 _88162 _88175 y f s) = (term54 _88162 _88175 y f s).
Proof. exact (@lem3394132 _88175 _88162 y f s). Qed.
Lemma lem3394134 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term55 _88162 _88175 x f P) = (term56 _88162 _88175 x f P).
Proof. exact (@lem3394133 _88162 _88175 x f (term57 _88175 P)). Qed.
Lemma lem3394144 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term58 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3394145 {_88175 : Type'} (p : _88175 -> Prop) (x : _88175) : (term58 _88175 x p) = (p x).
Proof. exact (@lem3394144 _88175 p x). Qed.
Lemma lem3394146 {_88175 : Type'} (P : _88175 -> Prop) (x : _88175) : (term58 _88175 x P) = (P x).
Proof. exact (@lem3394145 _88175 P x). Qed.
Lemma lem3394147 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term59 _88162 _88175 x f x') = (term59 _88162 _88175 x f x').
Proof. exact (eq_refl (term59 _88162 _88175 x f x')). Qed.
Lemma lem3394148 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term60 _88162 _88175 x f x' P) = (term61 _88162 _88175 x f P x').
Proof. exact (MK_COMB (@lem3394147 _88162 _88175 x f x') (@lem3394146 _88175 P x')). Qed.
Lemma lem3394151 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term62 _88162 _88175 x f P) = (term63 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394148 _88162 _88175 x f P x')). Qed.
Lemma lem3394152 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394153 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term56 _88162 _88175 x f P) = (term64 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394152 _88175) (@lem3394151 _88162 _88175 x f P)). Qed.
Lemma lem3394158 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term55 _88162 _88175 x f P) = (term64 _88162 _88175 x f P).
Proof. exact (TRANS (@lem3394134 _88162 _88175 x f P) (@lem3394153 _88162 _88175 x f P)). Qed.
Lemma lem3394159 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : ((term22 _88162 _88175 x P f) = (term55 _88162 _88175 x f P)) = ((term49 _88162 _88175 P x f) = (term64 _88162 _88175 x f P)).
Proof. exact (MK_COMB (@lem3394130 _88162 _88175 P x f) (@lem3394158 _88162 _88175 x f P)). Qed.
Lemma lem3394162 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : (term65 _88162 _88175 f P) = (term66 _88162 _88175 f P).
Proof. exact (fun_ext (fun x : _88162 => @lem3394159 _88162 _88175 x f P)). Qed.
Lemma lem3394163 {_88162 : Type'} : (@all _88162) = (@all _88162).
Proof. exact (eq_refl (@all _88162)). Qed.
Lemma lem3394164 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : (term3 _88162 _88175 f P) = (term67 _88162 _88175 f P).
Proof. exact (MK_COMB (@lem3394163 _88162) (@lem3394162 _88162 _88175 f P)). Qed.
Lemma lem3394169 {_88162 _88175 : Type'} (f : _88175 -> _88162) : (term5 _88162 _88175 f) = (term68 _88162 _88175 f).
Proof. exact (fun_ext (fun P : _88175 -> Prop => @lem3394164 _88162 _88175 f P)). Qed.
Lemma lem3394170 {_88175 : Type'} : (@all (_88175 -> Prop)) = (@all (_88175 -> Prop)).
Proof. exact (eq_refl (@all (_88175 -> Prop))). Qed.
Lemma lem3394171 {_88162 _88175 : Type'} (f : _88175 -> _88162) : (term7 _88162 _88175 f) = (term69 _88162 _88175 f).
Proof. exact (MK_COMB (@lem3394170 _88175) (@lem3394169 _88162 _88175 f)). Qed.
Lemma lem3394176 {_88162 _88175 : Type'} : (term9 _88162 _88175) = (term70 _88162 _88175).
Proof. exact (fun_ext (fun f : _88175 -> _88162 => @lem3394171 _88162 _88175 f)). Qed.
Lemma lem3394177 {_88162 _88175 : Type'} : (@all (_88175 -> _88162)) = (@all (_88175 -> _88162)).
Proof. exact (eq_refl (@all (_88175 -> _88162))). Qed.
Lemma lem3394178 {_88162 _88175 : Type'} : (term11 _88162 _88175) = (term71 _88162 _88175).
Proof. exact (MK_COMB (@lem3394177 _88162 _88175) (@lem3394176 _88162 _88175)). Qed.
Lemma lem3394183 {_88162 _88175 : Type'} : (term71 _88162 _88175) = (term11 _88162 _88175).
Proof. exact (SYM (@lem3394178 _88162 _88175)). Qed.
Lemma lem3394185 (p : Prop) : p = (term72 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3394186 {_88162 _88175 : Type'} : (term71 _88162 _88175) = (term73 _88162 _88175).
Proof. exact (@lem3394185 (term71 _88162 _88175)). Qed.
Lemma lem3394187 {_88162 _88175 : Type'} : (term73 _88162 _88175) = (term71 _88162 _88175).
Proof. exact (SYM (@lem3394186 _88162 _88175)). Qed.
Lemma lem3394188 {_88162 _88175 : Type'} (h1 : term74 _88162 _88175) : term74 _88162 _88175.
Proof. exact (h1). Qed.
Lemma lem3394191 {_88162 _88175 : Type'} (h1 : term73 _88162 _88175) : term73 _88162 _88175.
Proof. exact (h1). Qed.
Lemma lem3394192 {_88162 _88175 : Type'} : term75 _88162 _88175.
Proof. exact (fun h0 : term73 _88162 _88175 => @lem3394191 _88162 _88175 h0). Qed.
Lemma lem3394193 {_88162 _88175 : Type'} (h1 : term75 _88162 _88175) : term75 _88162 _88175.
Proof. exact (h1). Qed.
Lemma lem3394194 {_88162 _88175 : Type'} (h1 : term73 _88162 _88175) : term73 _88162 _88175.
Proof. exact (h1). Qed.
Lemma lem3394195 {_88162 _88175 : Type'} (h1 : term73 _88162 _88175) (h2 : term75 _88162 _88175) : term73 _88162 _88175.
Proof. exact (@lem3394193 _88162 _88175 h2 (@lem3394194 _88162 _88175 h1)). Qed.
Lemma lem3394196 {_88162 _88175 : Type'} (h1 : term73 _88162 _88175) : term76 _88162 _88175.
Proof. exact (fun h0 : term75 _88162 _88175 => @lem3394195 _88162 _88175 h1 h0). Qed.
Lemma lem3394197 {_88162 _88175 : Type'} (h1 : term75 _88162 _88175) : term75 _88162 _88175.
Proof. exact (h1). Qed.
Lemma lem3394198 {_88162 _88175 : Type'} (h1 : term73 _88162 _88175) (h2 : term75 _88162 _88175) : term73 _88162 _88175.
Proof. exact (@lem3394196 _88162 _88175 h1 (@lem3394197 _88162 _88175 h2)). Qed.
Lemma lem3394199 {_88162 _88175 : Type'} (h1 : term75 _88162 _88175) : term75 _88162 _88175.
Proof. exact (fun h0 : term73 _88162 _88175 => @lem3394198 _88162 _88175 h0 h1). Qed.
Lemma lem3394200 {_88162 _88175 : Type'} : term77 _88162 _88175.
Proof. exact (fun h0 : term75 _88162 _88175 => @lem3394199 _88162 _88175 h0). Qed.
Lemma lem3394203 {_88162 _88175 : Type'} : term75 _88162 _88175.
Proof. exact (@lem3394200 _88162 _88175 (@lem3394192 _88162 _88175)). Qed.
Lemma lem3394204 {_88162 _88175 : Type'} : term75 _88162 _88175.
Proof. exact (@lem3394203 _88162 _88175). Qed.
Lemma lem3394206 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3394207 {_88162 _88175 : Type'} : (term73 _88162 _88175) = (term78 _88162 _88175).
Proof. exact (@lem3394206 (term74 _88162 _88175)). Qed.
Lemma lem3394209 (t : Prop) : (term79 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3394210 {_88162 _88175 : Type'} : (term78 _88162 _88175) = (term71 _88162 _88175).
Proof. exact (@lem3394209 (term71 _88162 _88175)). Qed.
Lemma lem3394291 {_88162 _88175 : Type'} : (term73 _88162 _88175) = (term71 _88162 _88175).
Proof. exact (TRANS (@lem3394207 _88162 _88175) (@lem3394210 _88162 _88175)). Qed.
Lemma lem3394296 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term61 _88162 _88175 x f P x') = (term61 _88162 _88175 x f P x').
Proof. exact (eq_refl (term61 _88162 _88175 x f P x')). Qed.
Lemma lem3394297 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term63 _88162 _88175 x f P) = (term63 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394296 _88162 _88175 x f P x')). Qed.
Lemma lem3394298 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394299 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term64 _88162 _88175 x f P) = (term64 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394298 _88175) (@lem3394297 _88162 _88175 x f P)). Qed.
Lemma lem3394304 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term46 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x').
Proof. exact (eq_refl (term46 _88162 _88175 P x f x')). Qed.
Lemma lem3394305 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term48 _88162 _88175 P x f) = (term48 _88162 _88175 P x f).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394304 _88162 _88175 P x f x')). Qed.
Lemma lem3394306 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394307 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term49 _88162 _88175 P x f) = (term49 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394306 _88175) (@lem3394305 _88162 _88175 P x f)). Qed.
Lemma lem3394308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394309 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term50 _88162 _88175 P x f) = (term50 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394308) (@lem3394307 _88162 _88175 P x f)). Qed.
Lemma lem3394310 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : ((term49 _88162 _88175 P x f) = (term64 _88162 _88175 x f P)) = ((term49 _88162 _88175 P x f) = (term64 _88162 _88175 x f P)).
Proof. exact (MK_COMB (@lem3394309 _88162 _88175 P x f) (@lem3394299 _88162 _88175 x f P)). Qed.
Lemma lem3394311 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : (term66 _88162 _88175 f P) = (term66 _88162 _88175 f P).
Proof. exact (fun_ext (fun x : _88162 => @lem3394310 _88162 _88175 x f P)). Qed.
Lemma lem3394312 {_88162 : Type'} : (@all _88162) = (@all _88162).
Proof. exact (eq_refl (@all _88162)). Qed.
Lemma lem3394313 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : (term67 _88162 _88175 f P) = (term67 _88162 _88175 f P).
Proof. exact (MK_COMB (@lem3394312 _88162) (@lem3394311 _88162 _88175 f P)). Qed.
Lemma lem3394314 {_88162 _88175 : Type'} (f : _88175 -> _88162) : (term68 _88162 _88175 f) = (term68 _88162 _88175 f).
Proof. exact (fun_ext (fun P : _88175 -> Prop => @lem3394313 _88162 _88175 f P)). Qed.
Lemma lem3394315 {_88175 : Type'} : (@all (_88175 -> Prop)) = (@all (_88175 -> Prop)).
Proof. exact (eq_refl (@all (_88175 -> Prop))). Qed.
Lemma lem3394316 {_88162 _88175 : Type'} (f : _88175 -> _88162) : (term69 _88162 _88175 f) = (term69 _88162 _88175 f).
Proof. exact (MK_COMB (@lem3394315 _88175) (@lem3394314 _88162 _88175 f)). Qed.
Lemma lem3394317 {_88162 _88175 : Type'} : (term70 _88162 _88175) = (term70 _88162 _88175).
Proof. exact (fun_ext (fun f : _88175 -> _88162 => @lem3394316 _88162 _88175 f)). Qed.
Lemma lem3394318 {_88162 _88175 : Type'} : (@all (_88175 -> _88162)) = (@all (_88175 -> _88162)).
Proof. exact (eq_refl (@all (_88175 -> _88162))). Qed.
Lemma lem3394319 {_88162 _88175 : Type'} : (term71 _88162 _88175) = (term71 _88162 _88175).
Proof. exact (MK_COMB (@lem3394318 _88162 _88175) (@lem3394317 _88162 _88175)). Qed.
Lemma lem3394356 {_88162 _88175 : Type'} : (term73 _88162 _88175) = (term71 _88162 _88175).
Proof. exact (TRANS (@lem3394291 _88162 _88175) (@lem3394319 _88162 _88175)). Qed.
Lemma lem3394357 {_88162 _88175 : Type'} : (term71 _88162 _88175) = (term73 _88162 _88175).
Proof. exact (SYM (@lem3394356 _88162 _88175)). Qed.
Lemma lem3394359 (p : Prop) : p = (term72 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3394360 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : ((term49 _88162 _88175 P x f) = (term64 _88162 _88175 x f P)) = (term80 _88162 _88175 x f P).
Proof. exact (@lem3394359 ((term49 _88162 _88175 P x f) = (term64 _88162 _88175 x f P))). Qed.
Lemma lem3394361 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term80 _88162 _88175 x f P) = ((term49 _88162 _88175 P x f) = (term64 _88162 _88175 x f P)).
Proof. exact (SYM (@lem3394360 _88162 _88175 x f P)). Qed.
Lemma lem3394362 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term81 _88162 _88175 x f P) : term81 _88162 _88175 x f P.
Proof. exact (h1). Qed.
Lemma lem3394371 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term82 _88162 _88175 P x f x') = (term83 _88162 _88175 P x f x').
Proof. exact (@lem17045 (P x') (x = (f x'))). Qed.
Lemma lem3394374 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term46 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x').
Proof. exact (eq_refl (term46 _88162 _88175 P x f x')). Qed.
Lemma lem3394375 {_88175 : Type'} (P : _88175 -> Prop) : (term84 _88175 P) = (term85 _88175 P).
Proof. exact (@lem18394 _88175 P). Qed.
Lemma lem3394376 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term86 _88162 _88175 P x f) = (term87 _88162 _88175 P x f).
Proof. exact (@lem3394375 _88175 (term48 _88162 _88175 P x f)). Qed.
Lemma lem3394377 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term88 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x').
Proof. exact (eq_refl (term88 _88162 _88175 P x f x')). Qed.
Lemma lem3394378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3394379 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term89 _88162 _88175 P x f x') = (term82 _88162 _88175 P x f x').
Proof. exact (MK_COMB (@lem3394378) (@lem3394377 _88162 _88175 P x f x')). Qed.
Lemma lem3394380 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term89 _88162 _88175 P x f x') = (term83 _88162 _88175 P x f x').
Proof. exact (TRANS (@lem3394379 _88162 _88175 P x f x') (@lem3394371 _88162 _88175 P x f x')). Qed.
Lemma lem3394381 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term90 _88162 _88175 P x f) = (term91 _88162 _88175 P x f).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394380 _88162 _88175 P x f x')). Qed.
Lemma lem3394382 {_88175 : Type'} : (@all _88175) = (@all _88175).
Proof. exact (eq_refl (@all _88175)). Qed.
Lemma lem3394383 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term87 _88162 _88175 P x f) = (term92 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394382 _88175) (@lem3394381 _88162 _88175 P x f)). Qed.
Lemma lem3394384 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term86 _88162 _88175 P x f) = (term92 _88162 _88175 P x f).
Proof. exact (TRANS (@lem3394376 _88162 _88175 P x f) (@lem3394383 _88162 _88175 P x f)). Qed.
Lemma lem3394385 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term48 _88162 _88175 P x f) = (term48 _88162 _88175 P x f).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394374 _88162 _88175 P x f x')). Qed.
Lemma lem3394386 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394387 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term49 _88162 _88175 P x f) = (term49 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394386 _88175) (@lem3394385 _88162 _88175 P x f)). Qed.
Lemma lem3394396 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term93 _88162 _88175 x f P x') = (term94 _88162 _88175 x f P x').
Proof. exact (@lem17045 (x = (f x')) (P x')). Qed.
Lemma lem3394399 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term61 _88162 _88175 x f P x') = (term61 _88162 _88175 x f P x').
Proof. exact (eq_refl (term61 _88162 _88175 x f P x')). Qed.
Lemma lem3394400 {_88175 : Type'} (P : _88175 -> Prop) : (term84 _88175 P) = (term85 _88175 P).
Proof. exact (@lem18394 _88175 P). Qed.
Lemma lem3394401 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term95 _88162 _88175 x f P) = (term96 _88162 _88175 x f P).
Proof. exact (@lem3394400 _88175 (term63 _88162 _88175 x f P)). Qed.
Lemma lem3394402 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term97 _88162 _88175 x f P x') = (term61 _88162 _88175 x f P x').
Proof. exact (eq_refl (term97 _88162 _88175 x f P x')). Qed.
Lemma lem3394403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3394404 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term98 _88162 _88175 x f P x') = (term93 _88162 _88175 x f P x').
Proof. exact (MK_COMB (@lem3394403) (@lem3394402 _88162 _88175 x f P x')). Qed.
Lemma lem3394405 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term98 _88162 _88175 x f P x') = (term94 _88162 _88175 x f P x').
Proof. exact (TRANS (@lem3394404 _88162 _88175 x f P x') (@lem3394396 _88162 _88175 x f P x')). Qed.
Lemma lem3394406 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term99 _88162 _88175 x f P) = (term100 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394405 _88162 _88175 x f P x')). Qed.
Lemma lem3394407 {_88175 : Type'} : (@all _88175) = (@all _88175).
Proof. exact (eq_refl (@all _88175)). Qed.
Lemma lem3394408 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term96 _88162 _88175 x f P) = (term101 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394407 _88175) (@lem3394406 _88162 _88175 x f P)). Qed.
Lemma lem3394409 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term95 _88162 _88175 x f P) = (term101 _88162 _88175 x f P).
Proof. exact (TRANS (@lem3394401 _88162 _88175 x f P) (@lem3394408 _88162 _88175 x f P)). Qed.
Lemma lem3394410 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term63 _88162 _88175 x f P) = (term63 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394399 _88162 _88175 x f P x')). Qed.
Lemma lem3394411 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394412 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term64 _88162 _88175 x f P) = (term64 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394411 _88175) (@lem3394410 _88162 _88175 x f P)). Qed.
Lemma lem3394413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3394414 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term102 _88162 _88175 P x f) = (term103 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394413) (@lem3394384 _88162 _88175 P x f)). Qed.
Lemma lem3394415 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term104 _88162 _88175 x f P) = (term105 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394414 _88162 _88175 P x f) (@lem3394412 _88162 _88175 x f P)). Qed.
Lemma lem3394416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3394417 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term106 _88162 _88175 P x f) = (term106 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394416) (@lem3394387 _88162 _88175 P x f)). Qed.
Lemma lem3394418 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term107 _88162 _88175 x f P) = (term108 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394417 _88162 _88175 P x f) (@lem3394409 _88162 _88175 x f P)). Qed.
Lemma lem3394419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3394420 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term109 _88162 _88175 x f P) = (term110 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394419) (@lem3394418 _88162 _88175 x f P)). Qed.
Lemma lem3394421 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term111 _88162 _88175 x f P) = (term112 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394420 _88162 _88175 x f P) (@lem3394415 _88162 _88175 x f P)). Qed.
Lemma lem3394422 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term81 _88162 _88175 x f P) = (term111 _88162 _88175 x f P).
Proof. exact (@lem17646 (term49 _88162 _88175 P x f) (term64 _88162 _88175 x f P)). Qed.
Lemma lem3394423 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term81 _88162 _88175 x f P) = (term112 _88162 _88175 x f P).
Proof. exact (TRANS (@lem3394422 _88162 _88175 x f P) (@lem3394421 _88162 _88175 x f P)). Qed.
Lemma lem3394582 {A : Type'} (P : A -> Prop) (Q : Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3394583 {_88175 : Type'} (P : _88175 -> Prop) (Q : Prop) : (term113 _88175 P Q) = (term114 _88175 P Q).
Proof. exact (@lem3394582 _88175 P Q). Qed.
Lemma lem3394584 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term115 _88162 _88175 x f P) = (term116 _88162 _88175 x f P).
Proof. exact (@lem3394583 _88175 (term48 _88162 _88175 P x f) (term101 _88162 _88175 x f P)). Qed.
Lemma lem3394585 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term88 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x').
Proof. exact (eq_refl (term88 _88162 _88175 P x f x')). Qed.
Lemma lem3394586 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term117 _88162 _88175 P x f) = (term48 _88162 _88175 P x f).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394585 _88162 _88175 P x f x')). Qed.
Lemma lem3394587 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394588 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term118 _88162 _88175 P x f) = (term49 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394587 _88175) (@lem3394586 _88162 _88175 P x f)). Qed.
Lemma lem3394589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3394590 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term119 _88162 _88175 P x f) = (term106 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394589) (@lem3394588 _88162 _88175 P x f)). Qed.
Lemma lem3394591 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term101 _88162 _88175 x f P) = (term101 _88162 _88175 x f P).
Proof. exact (eq_refl (term101 _88162 _88175 x f P)). Qed.
Lemma lem3394592 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term115 _88162 _88175 x f P) = (term108 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394590 _88162 _88175 P x f) (@lem3394591 _88162 _88175 x f P)). Qed.
Lemma lem3394593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394594 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term120 _88162 _88175 x f P) = (term121 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394593) (@lem3394592 _88162 _88175 x f P)). Qed.
Lemma lem3394595 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term88 _88162 _88175 P x f x') = (term46 _88162 _88175 P x f x').
Proof. exact (eq_refl (term88 _88162 _88175 P x f x')). Qed.
Lemma lem3394596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3394597 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term122 _88162 _88175 P x f x') = (term123 _88162 _88175 P x f x').
Proof. exact (MK_COMB (@lem3394596) (@lem3394595 _88162 _88175 P x f x')). Qed.
Lemma lem3394598 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term101 _88162 _88175 x f P) = (term101 _88162 _88175 x f P).
Proof. exact (eq_refl (term101 _88162 _88175 x f P)). Qed.
Lemma lem3394599 {_88162 _88175 : Type'} (x : _88175) (x' : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term124 _88162 _88175 x x' f P) = (term125 _88162 _88175 x x' f P).
Proof. exact (MK_COMB (@lem3394597 _88162 _88175 P x' f x) (@lem3394598 _88162 _88175 x' f P)). Qed.
Lemma lem3394600 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term126 _88162 _88175 x f P) = (term127 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394599 _88162 _88175 x' x f P)). Qed.
Lemma lem3394601 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394602 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term116 _88162 _88175 x f P) = (term128 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394601 _88175) (@lem3394600 _88162 _88175 x f P)). Qed.
Lemma lem3394603 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : ((term115 _88162 _88175 x f P) = (term116 _88162 _88175 x f P)) = ((term108 _88162 _88175 x f P) = (term128 _88162 _88175 x f P)).
Proof. exact (MK_COMB (@lem3394594 _88162 _88175 x f P) (@lem3394602 _88162 _88175 x f P)). Qed.
Lemma lem3394604 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term108 _88162 _88175 x f P) = (term128 _88162 _88175 x f P).
Proof. exact (EQ_MP (@lem3394603 _88162 _88175 x f P) (@lem3394584 _88162 _88175 x f P)). Qed.
Lemma lem3394605 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3394606 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term110 _88162 _88175 x f P) = (term129 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394605) (@lem3394604 _88162 _88175 x f P)). Qed.
Lemma lem3394608 {A : Type'} (P : Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3394609 {_88175 : Type'} (P : Prop) (Q : _88175 -> Prop) : (term130 _88175 P Q) = (term131 _88175 P Q).
Proof. exact (@lem3394608 _88175 P Q). Qed.
Lemma lem3394610 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term132 _88162 _88175 x f P) = (term133 _88162 _88175 x f P).
Proof. exact (@lem3394609 _88175 (term92 _88162 _88175 P x f) (term63 _88162 _88175 x f P)). Qed.
Lemma lem3394611 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term97 _88162 _88175 x f P x') = (term61 _88162 _88175 x f P x').
Proof. exact (eq_refl (term97 _88162 _88175 x f P x')). Qed.
Lemma lem3394612 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term134 _88162 _88175 x f P) = (term63 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394611 _88162 _88175 x f P x')). Qed.
Lemma lem3394613 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394614 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term135 _88162 _88175 x f P) = (term64 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394613 _88175) (@lem3394612 _88162 _88175 x f P)). Qed.
Lemma lem3394615 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term103 _88162 _88175 P x f) = (term103 _88162 _88175 P x f).
Proof. exact (eq_refl (term103 _88162 _88175 P x f)). Qed.
Lemma lem3394616 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term132 _88162 _88175 x f P) = (term105 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394615 _88162 _88175 P x f) (@lem3394614 _88162 _88175 x f P)). Qed.
Lemma lem3394617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394618 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term136 _88162 _88175 x f P) = (term137 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394617) (@lem3394616 _88162 _88175 x f P)). Qed.
Lemma lem3394619 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term97 _88162 _88175 x f P x') = (term61 _88162 _88175 x f P x').
Proof. exact (eq_refl (term97 _88162 _88175 x f P x')). Qed.
Lemma lem3394620 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term103 _88162 _88175 P x f) = (term103 _88162 _88175 P x f).
Proof. exact (eq_refl (term103 _88162 _88175 P x f)). Qed.
Lemma lem3394621 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term138 _88162 _88175 x f P x') = (term139 _88162 _88175 x f P x').
Proof. exact (MK_COMB (@lem3394620 _88162 _88175 P x f) (@lem3394619 _88162 _88175 x f P x')). Qed.
Lemma lem3394622 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term140 _88162 _88175 x f P) = (term141 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394621 _88162 _88175 x f P x')). Qed.
Lemma lem3394623 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394624 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term133 _88162 _88175 x f P) = (term142 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394623 _88175) (@lem3394622 _88162 _88175 x f P)). Qed.
Lemma lem3394625 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : ((term132 _88162 _88175 x f P) = (term133 _88162 _88175 x f P)) = ((term105 _88162 _88175 x f P) = (term142 _88162 _88175 x f P)).
Proof. exact (MK_COMB (@lem3394618 _88162 _88175 x f P) (@lem3394624 _88162 _88175 x f P)). Qed.
Lemma lem3394626 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term105 _88162 _88175 x f P) = (term142 _88162 _88175 x f P).
Proof. exact (EQ_MP (@lem3394625 _88162 _88175 x f P) (@lem3394610 _88162 _88175 x f P)). Qed.
Lemma lem3394627 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term112 _88162 _88175 x f P) = (term143 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394606 _88162 _88175 x f P) (@lem3394626 _88162 _88175 x f P)). Qed.
Lemma lem3394629 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3394630 {_88175 : Type'} (P : _88175 -> Prop) (Q : _88175 -> Prop) : (term144 _88175 P Q) = (term145 _88175 P Q).
Proof. exact (@lem3394629 _88175 P Q). Qed.
Lemma lem3394631 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term146 _88162 _88175 x f P) = (term147 _88162 _88175 x f P).
Proof. exact (@lem3394630 _88175 (term127 _88162 _88175 x f P) (term141 _88162 _88175 x f P)). Qed.
Lemma lem3394632 {_88162 _88175 : Type'} (x : _88175) (x' : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term148 _88162 _88175 x' f P x) = (term125 _88162 _88175 x x' f P).
Proof. exact (eq_refl (term148 _88162 _88175 x' f P x)). Qed.
Lemma lem3394633 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term149 _88162 _88175 x f P) = (term127 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394632 _88162 _88175 x' x f P)). Qed.
Lemma lem3394634 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394635 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term150 _88162 _88175 x f P) = (term128 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394634 _88175) (@lem3394633 _88162 _88175 x f P)). Qed.
Lemma lem3394636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3394637 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term151 _88162 _88175 x f P) = (term129 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394636) (@lem3394635 _88162 _88175 x f P)). Qed.
Lemma lem3394638 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term152 _88162 _88175 x f P x') = (term139 _88162 _88175 x f P x').
Proof. exact (eq_refl (term152 _88162 _88175 x f P x')). Qed.
Lemma lem3394639 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term153 _88162 _88175 x f P) = (term141 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394638 _88162 _88175 x f P x')). Qed.
Lemma lem3394640 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394641 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term154 _88162 _88175 x f P) = (term142 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394640 _88175) (@lem3394639 _88162 _88175 x f P)). Qed.
Lemma lem3394642 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term146 _88162 _88175 x f P) = (term143 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394637 _88162 _88175 x f P) (@lem3394641 _88162 _88175 x f P)). Qed.
Lemma lem3394643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394644 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term155 _88162 _88175 x f P) = (term156 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394643) (@lem3394642 _88162 _88175 x f P)). Qed.
Lemma lem3394645 {_88162 _88175 : Type'} (x : _88175) (x' : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term148 _88162 _88175 x' f P x) = (term125 _88162 _88175 x x' f P).
Proof. exact (eq_refl (term148 _88162 _88175 x' f P x)). Qed.
Lemma lem3394646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3394647 {_88162 _88175 : Type'} (x : _88175) (x' : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term157 _88162 _88175 x' f P x) = (term158 _88162 _88175 x x' f P).
Proof. exact (MK_COMB (@lem3394646) (@lem3394645 _88162 _88175 x x' f P)). Qed.
Lemma lem3394648 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term152 _88162 _88175 x f P x') = (term139 _88162 _88175 x f P x').
Proof. exact (eq_refl (term152 _88162 _88175 x f P x')). Qed.
Lemma lem3394649 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term159 _88162 _88175 x f P x') = (term160 _88162 _88175 x f P x').
Proof. exact (MK_COMB (@lem3394647 _88162 _88175 x' x f P) (@lem3394648 _88162 _88175 x f P x')). Qed.
Lemma lem3394650 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term161 _88162 _88175 x f P) = (term162 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394649 _88162 _88175 x f P x')). Qed.
Lemma lem3394651 {_88175 : Type'} : (@ex _88175) = (@ex _88175).
Proof. exact (eq_refl (@ex _88175)). Qed.
Lemma lem3394652 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term147 _88162 _88175 x f P) = (term163 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394651 _88175) (@lem3394650 _88162 _88175 x f P)). Qed.
Lemma lem3394653 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : ((term146 _88162 _88175 x f P) = (term147 _88162 _88175 x f P)) = ((term143 _88162 _88175 x f P) = (term163 _88162 _88175 x f P)).
Proof. exact (MK_COMB (@lem3394644 _88162 _88175 x f P) (@lem3394652 _88162 _88175 x f P)). Qed.
Lemma lem3394654 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term143 _88162 _88175 x f P) = (term163 _88162 _88175 x f P).
Proof. exact (EQ_MP (@lem3394653 _88162 _88175 x f P) (@lem3394631 _88162 _88175 x f P)). Qed.
Lemma lem3394656 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term112 _88162 _88175 x f P) = (term163 _88162 _88175 x f P).
Proof. exact (TRANS (@lem3394627 _88162 _88175 x f P) (@lem3394654 _88162 _88175 x f P)). Qed.
Lemma lem3394657 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term81 _88162 _88175 x f P) = (term163 _88162 _88175 x f P).
Proof. exact (TRANS (@lem3394423 _88162 _88175 x f P) (@lem3394656 _88162 _88175 x f P)). Qed.
Lemma lem3394658 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term81 _88162 _88175 x f P) : term163 _88162 _88175 x f P.
Proof. exact (EQ_MP (@lem3394657 _88162 _88175 x f P) (@lem3394362 _88162 _88175 x f P h1)). Qed.
Lemma lem3394659 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term160 _88162 _88175 x f P x') : term160 _88162 _88175 x f P x'.
Proof. exact (h1). Qed.
Lemma lem3394672 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term61 _88162 _88175 x f P x') = (term61 _88162 _88175 x f P x').
Proof. exact (eq_refl (term61 _88162 _88175 x f P x')). Qed.
Lemma lem3394689 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term83 _88162 _88175 P x f x') = (term83 _88162 _88175 P x f x').
Proof. exact (eq_refl (term83 _88162 _88175 P x f x')). Qed.
Lemma lem3394690 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term91 _88162 _88175 P x f) = (term91 _88162 _88175 P x f).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394689 _88162 _88175 P x f x')). Qed.
Lemma lem3394691 {_88175 : Type'} : (@all _88175) = (@all _88175).
Proof. exact (eq_refl (@all _88175)). Qed.
Lemma lem3394692 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term92 _88162 _88175 P x f) = (term92 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394691 _88175) (@lem3394690 _88162 _88175 P x f)). Qed.
Lemma lem3394693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3394694 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term103 _88162 _88175 P x f) = (term103 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394693) (@lem3394692 _88162 _88175 P x f)). Qed.
Lemma lem3394695 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term139 _88162 _88175 x f P x') = (term139 _88162 _88175 x f P x').
Proof. exact (MK_COMB (@lem3394694 _88162 _88175 P x f) (@lem3394672 _88162 _88175 x f P x')). Qed.
Lemma lem3394712 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term94 _88162 _88175 x f P x') = (term94 _88162 _88175 x f P x').
Proof. exact (eq_refl (term94 _88162 _88175 x f P x')). Qed.
Lemma lem3394713 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term100 _88162 _88175 x f P) = (term100 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394712 _88162 _88175 x f P x')). Qed.
Lemma lem3394714 {_88175 : Type'} : (@all _88175) = (@all _88175).
Proof. exact (eq_refl (@all _88175)). Qed.
Lemma lem3394715 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term101 _88162 _88175 x f P) = (term101 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394714 _88175) (@lem3394713 _88162 _88175 x f P)). Qed.
Lemma lem3394730 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term123 _88162 _88175 P x f x') = (term123 _88162 _88175 P x f x').
Proof. exact (eq_refl (term123 _88162 _88175 P x f x')). Qed.
Lemma lem3394731 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term125 _88162 _88175 x' x f P) = (term125 _88162 _88175 x' x f P).
Proof. exact (MK_COMB (@lem3394730 _88162 _88175 P x f x') (@lem3394715 _88162 _88175 x f P)). Qed.
Lemma lem3394732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3394733 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term158 _88162 _88175 x' x f P) = (term158 _88162 _88175 x' x f P).
Proof. exact (MK_COMB (@lem3394732) (@lem3394731 _88162 _88175 x' x f P)). Qed.
Lemma lem3394734 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term160 _88162 _88175 x f P x') = (term160 _88162 _88175 x f P x').
Proof. exact (MK_COMB (@lem3394733 _88162 _88175 x' x f P) (@lem3394695 _88162 _88175 x f P x')). Qed.
Lemma lem3394735 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term160 _88162 _88175 x f P x') : term160 _88162 _88175 x f P x'.
Proof. exact (EQ_MP (@lem3394734 _88162 _88175 x f P x') (@lem3394659 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394736 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term125 _88162 _88175 x' x f P.
Proof. exact (h1). Qed.
Lemma lem3394737 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term139 _88162 _88175 x f P x'.
Proof. exact (h1). Qed.
Lemma lem3394738 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term101 _88162 _88175 x f P.
Proof. exact (proj2 (@lem3394736 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394739 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term46 _88162 _88175 P x f x'.
Proof. exact (proj1 (@lem3394736 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394742 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term61 _88162 _88175 x f P x'.
Proof. exact (proj2 (@lem3394737 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394743 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term92 _88162 _88175 P x f.
Proof. exact (proj1 (@lem3394737 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394753 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) : (term94 _88162 _88175 x f P x') = (term94 _88162 _88175 x f P x').
Proof. exact (eq_refl (term94 _88162 _88175 x f P x')). Qed.
Lemma lem3394754 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term100 _88162 _88175 x f P) = (term100 _88162 _88175 x f P).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394753 _88162 _88175 x f P x')). Qed.
Lemma lem3394755 {_88175 : Type'} : (@all _88175) = (@all _88175).
Proof. exact (eq_refl (@all _88175)). Qed.
Lemma lem3394757 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term101 _88162 _88175 x f P) = (term101 _88162 _88175 x f P).
Proof. exact (MK_COMB (@lem3394755 _88175) (@lem3394754 _88162 _88175 x f P)). Qed.
Lemma lem3394758 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term101 _88162 _88175 x f P.
Proof. exact (EQ_MP (@lem3394757 _88162 _88175 x f P) (@lem3394738 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394774 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (x' : _88175) : (term83 _88162 _88175 P x f x') = (term83 _88162 _88175 P x f x').
Proof. exact (eq_refl (term83 _88162 _88175 P x f x')). Qed.
Lemma lem3394775 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term91 _88162 _88175 P x f) = (term91 _88162 _88175 P x f).
Proof. exact (fun_ext (fun x' : _88175 => @lem3394774 _88162 _88175 P x f x')). Qed.
Lemma lem3394776 {_88175 : Type'} : (@all _88175) = (@all _88175).
Proof. exact (eq_refl (@all _88175)). Qed.
Lemma lem3394778 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) : (term92 _88162 _88175 P x f) = (term92 _88162 _88175 P x f).
Proof. exact (MK_COMB (@lem3394776 _88175) (@lem3394775 _88162 _88175 P x f)). Qed.
Lemma lem3394779 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term92 _88162 _88175 P x f.
Proof. exact (EQ_MP (@lem3394778 _88162 _88175 P x f) (@lem3394743 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394788 {_88162 _88175 : Type'} (_35734 : _88175) (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term164 _88162 _88175 x f P _35734.
Proof. exact (@lem3394758 _88162 _88175 x' x f P h1 _35734). Qed.
Lemma lem3394789 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term164 _88162 _88175 x f P _35734) = (term94 _88162 _88175 x f P _35734).
Proof. exact (eq_refl (term164 _88162 _88175 x f P _35734)). Qed.
Lemma lem3394791 {_88162 _88175 : Type'} (_35735 : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term165 _88162 _88175 P x f _35735.
Proof. exact (@lem3394779 _88162 _88175 x f P x' h1 _35735). Qed.
Lemma lem3394792 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (_35735 : _88175) : (term165 _88162 _88175 P x f _35735) = (term83 _88162 _88175 P x f _35735).
Proof. exact (eq_refl (term165 _88162 _88175 P x f _35735)). Qed.
Lemma lem3394799 {_88162 _88175 : Type'} (_35734 : _88175) (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term94 _88162 _88175 x f P _35734.
Proof. exact (EQ_MP (@lem3394789 _88162 _88175 x f P _35734) (@lem3394788 _88162 _88175 _35734 x' x f P h1)). Qed.
Lemma lem3394803 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : x = (f x').
Proof. exact (proj2 (@lem3394739 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394809 {_88162 _88175 : Type'} (_35735 : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term83 _88162 _88175 P x f _35735.
Proof. exact (EQ_MP (@lem3394792 _88162 _88175 P x f _35735) (@lem3394791 _88162 _88175 _35735 x f P x' h1)). Qed.
Lemma lem3394811 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : x = (f x').
Proof. exact (proj1 (@lem3394742 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394828 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term166 _88162 _88175 f P _35734) = (term166 _88162 _88175 f P _35734).
Proof. exact (eq_refl (term166 _88162 _88175 f P _35734)). Qed.
Lemma lem3394829 {_88162 _88175 : Type'} (_35734 : _88175) (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : (term167 _88162 _88175 f P _35734 x) = (term168 _88162 _88175 P _35734 f x').
Proof. exact (MK_COMB (@lem3394828 _88162 _88175 f P _35734) (@lem3394803 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394830 {_88162 _88175 : Type'} (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term168 _88162 _88175 P _35734 f x') = (term169 _88162 _88175 x' f P _35734).
Proof. exact (eq_refl (term168 _88162 _88175 P _35734 f x')). Qed.
Lemma lem3394831 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) (x : _88162) : (term170 _88162 _88175 f P _35734 x) = (term170 _88162 _88175 f P _35734 x).
Proof. exact (eq_refl (term170 _88162 _88175 f P _35734 x)). Qed.
Lemma lem3394832 {_88162 _88175 : Type'} (x : _88162) (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : ((term167 _88162 _88175 f P _35734 x) = (term168 _88162 _88175 P _35734 f x')) = ((term167 _88162 _88175 f P _35734 x) = (term169 _88162 _88175 x' f P _35734)).
Proof. exact (MK_COMB (@lem3394831 _88162 _88175 f P _35734 x) (@lem3394830 _88162 _88175 x' f P _35734)). Qed.
Lemma lem3394833 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term167 _88162 _88175 f P _35734 x) = (term94 _88162 _88175 x f P _35734).
Proof. exact (eq_refl (term167 _88162 _88175 f P _35734 x)). Qed.
Lemma lem3394834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394835 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term170 _88162 _88175 f P _35734 x) = (term171 _88162 _88175 x f P _35734).
Proof. exact (MK_COMB (@lem3394834) (@lem3394833 _88162 _88175 x f P _35734)). Qed.
Lemma lem3394836 {_88162 _88175 : Type'} (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term169 _88162 _88175 x' f P _35734) = (term169 _88162 _88175 x' f P _35734).
Proof. exact (eq_refl (term169 _88162 _88175 x' f P _35734)). Qed.
Lemma lem3394837 {_88162 _88175 : Type'} (x : _88162) (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : ((term167 _88162 _88175 f P _35734 x) = (term169 _88162 _88175 x' f P _35734)) = ((term94 _88162 _88175 x f P _35734) = (term169 _88162 _88175 x' f P _35734)).
Proof. exact (MK_COMB (@lem3394835 _88162 _88175 x f P _35734) (@lem3394836 _88162 _88175 x' f P _35734)). Qed.
Lemma lem3394838 {_88162 _88175 : Type'} (x : _88162) (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : ((term167 _88162 _88175 f P _35734 x) = (term168 _88162 _88175 P _35734 f x')) = ((term94 _88162 _88175 x f P _35734) = (term169 _88162 _88175 x' f P _35734)).
Proof. exact (TRANS (@lem3394832 _88162 _88175 x x' f P _35734) (@lem3394837 _88162 _88175 x x' f P _35734)). Qed.
Lemma lem3394839 {_88162 _88175 : Type'} (_35734 : _88175) (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : (term94 _88162 _88175 x f P _35734) = (term169 _88162 _88175 x' f P _35734).
Proof. exact (EQ_MP (@lem3394838 _88162 _88175 x x' f P _35734) (@lem3394829 _88162 _88175 _35734 x' x f P h1)). Qed.
Lemma lem3394840 {_88162 _88175 : Type'} (_35734 : _88175) (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term169 _88162 _88175 x' f P _35734.
Proof. exact (EQ_MP (@lem3394839 _88162 _88175 _35734 x' x f P h1) (@lem3394799 _88162 _88175 _35734 x' x f P h1)). Qed.
Lemma lem3394869 {_88162 _88175 : Type'} (P : _88175 -> Prop) (f : _88175 -> _88162) (_35735 : _88175) : (term172 _88162 _88175 P f _35735) = (term172 _88162 _88175 P f _35735).
Proof. exact (eq_refl (term172 _88162 _88175 P f _35735)). Qed.
Lemma lem3394870 {_88162 _88175 : Type'} (_35735 : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : (term173 _88162 _88175 P f _35735 x) = (term174 _88162 _88175 P _35735 f x').
Proof. exact (MK_COMB (@lem3394869 _88162 _88175 P f _35735) (@lem3394811 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394871 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : (term174 _88162 _88175 P _35735 f x') = (term175 _88162 _88175 P x' f _35735).
Proof. exact (eq_refl (term174 _88162 _88175 P _35735 f x')). Qed.
Lemma lem3394872 {_88162 _88175 : Type'} (P : _88175 -> Prop) (f : _88175 -> _88162) (_35735 : _88175) (x : _88162) : (term176 _88162 _88175 P f _35735 x) = (term176 _88162 _88175 P f _35735 x).
Proof. exact (eq_refl (term176 _88162 _88175 P f _35735 x)). Qed.
Lemma lem3394873 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : ((term173 _88162 _88175 P f _35735 x) = (term174 _88162 _88175 P _35735 f x')) = ((term173 _88162 _88175 P f _35735 x) = (term175 _88162 _88175 P x' f _35735)).
Proof. exact (MK_COMB (@lem3394872 _88162 _88175 P f _35735 x) (@lem3394871 _88162 _88175 P x' f _35735)). Qed.
Lemma lem3394874 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (_35735 : _88175) : (term173 _88162 _88175 P f _35735 x) = (term83 _88162 _88175 P x f _35735).
Proof. exact (eq_refl (term173 _88162 _88175 P f _35735 x)). Qed.
Lemma lem3394875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3394876 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x : _88162) (f : _88175 -> _88162) (_35735 : _88175) : (term176 _88162 _88175 P f _35735 x) = (term177 _88162 _88175 P x f _35735).
Proof. exact (MK_COMB (@lem3394875) (@lem3394874 _88162 _88175 P x f _35735)). Qed.
Lemma lem3394877 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : (term175 _88162 _88175 P x' f _35735) = (term175 _88162 _88175 P x' f _35735).
Proof. exact (eq_refl (term175 _88162 _88175 P x' f _35735)). Qed.
Lemma lem3394878 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : ((term173 _88162 _88175 P f _35735 x) = (term175 _88162 _88175 P x' f _35735)) = ((term83 _88162 _88175 P x f _35735) = (term175 _88162 _88175 P x' f _35735)).
Proof. exact (MK_COMB (@lem3394876 _88162 _88175 P x f _35735) (@lem3394877 _88162 _88175 P x' f _35735)). Qed.
Lemma lem3394879 {_88162 _88175 : Type'} (x : _88162) (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : ((term173 _88162 _88175 P f _35735 x) = (term174 _88162 _88175 P _35735 f x')) = ((term83 _88162 _88175 P x f _35735) = (term175 _88162 _88175 P x' f _35735)).
Proof. exact (TRANS (@lem3394873 _88162 _88175 x P x' f _35735) (@lem3394878 _88162 _88175 x P x' f _35735)). Qed.
Lemma lem3394880 {_88162 _88175 : Type'} (_35735 : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : (term83 _88162 _88175 P x f _35735) = (term175 _88162 _88175 P x' f _35735).
Proof. exact (EQ_MP (@lem3394879 _88162 _88175 x P x' f _35735) (@lem3394870 _88162 _88175 _35735 x f P x' h1)). Qed.
Lemma lem3394881 {_88162 _88175 : Type'} (_35735 : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term175 _88162 _88175 P x' f _35735.
Proof. exact (EQ_MP (@lem3394880 _88162 _88175 _35735 x f P x' h1) (@lem3394809 _88162 _88175 _35735 x f P x' h1)). Qed.
Lemma lem3394921 {_88162 : Type'} (x : _88162) : x = x.
Proof. exact (@lem21386 _88162 x). Qed.
Lemma lem3394922 {_88162 : Type'} (x : _88162) : x = x.
Proof. exact (@lem3394921 _88162 x). Qed.
Lemma lem3394923 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : (f x') = (f x').
Proof. exact (@lem3394922 _88162 (f x')). Qed.
Lemma lem3394924 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : term178 _88162 _88175 f x'.
Proof. exact (fun h0 : term179 _88162 _88175 f x' => @lem3394923 _88162 _88175 f x'). Qed.
Lemma lem3394926 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3394927 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : (term178 _88162 _88175 f x') = ((f x') = (f x')).
Proof. exact (@lem3394926 ((f x') = (f x'))). Qed.
Lemma lem3394928 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3394927 _88162 _88175 f x') (@lem3394924 _88162 _88175 f x')). Qed.
Lemma lem3394930 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : P x'.
Proof. exact (proj1 (@lem3394739 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394931 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term181 _88175 P x'.
Proof. exact (fun h0 : term182 _88175 P x' => @lem3394930 _88162 _88175 x' x f P h1). Qed.
Lemma lem3394933 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3394934 {_88175 : Type'} (P : _88175 -> Prop) (x' : _88175) : (term181 _88175 P x') = (P x').
Proof. exact (@lem3394933 (P x')). Qed.
Lemma lem3394935 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : P x'.
Proof. exact (EQ_MP (@lem3394934 _88175 P x') (@lem3394931 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394937 (a : Prop) (b : Prop) : (term183 a b) = (term184 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3394938 {_88162 _88175 : Type'} (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term169 _88162 _88175 x' f P _35734) = (term185 _88162 _88175 x' f P _35734).
Proof. exact (@lem3394937 ((f x') = (f _35734)) (P _35734)). Qed.
Lemma lem3394940 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3394941 {_88162 _88175 : Type'} (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term185 _88162 _88175 x' f P _35734) = (term186 _88162 _88175 x' f P _35734).
Proof. exact (@lem3394940 (term187 _88162 _88175 x' f P _35734)). Qed.
Lemma lem3394942 {_88162 _88175 : Type'} (x' : _88175) (f : _88175 -> _88162) (P : _88175 -> Prop) (_35734 : _88175) : (term169 _88162 _88175 x' f P _35734) = (term186 _88162 _88175 x' f P _35734).
Proof. exact (TRANS (@lem3394938 _88162 _88175 x' f P _35734) (@lem3394941 _88162 _88175 x' f P _35734)). Qed.
Lemma lem3394944 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term188 _88162 _88175 f P x'.
Proof. exact (conj (@lem3394928 _88162 _88175 f x') (@lem3394935 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394946 {_88162 _88175 : Type'} (_35734 : _88175) (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term186 _88162 _88175 x' f P _35734.
Proof. exact (EQ_MP (@lem3394942 _88162 _88175 x' f P _35734) (@lem3394840 _88162 _88175 _35734 x' x f P h1)). Qed.
Lemma lem3394947 {_88162 _88175 : Type'} (_35734 : _88175) (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term186 _88162 _88175 x' f P _35734.
Proof. exact (@lem3394946 _88162 _88175 _35734 x' x f P h1). Qed.
Lemma lem3394948 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term189 _88162 _88175 f P x'.
Proof. exact (@lem3394947 _88162 _88175 x' x' x f P h1). Qed.
Lemma lem3394951 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : False.
Proof. exact (@lem3394948 _88162 _88175 x' x f P h1 (@lem3394944 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3394952 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : term190.
Proof. exact (fun h0 : ~ False => @lem3394951 _88162 _88175 x' x f P h1). Qed.
Lemma lem3394954 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3394955 : term190 = False.
Proof. exact (@lem3394954 False). Qed.
Lemma lem3394982 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : P x'.
Proof. exact (proj2 (@lem3394742 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394983 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term181 _88175 P x'.
Proof. exact (fun h0 : term182 _88175 P x' => @lem3394982 _88162 _88175 x f P x' h1). Qed.
Lemma lem3394985 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3394986 {_88175 : Type'} (P : _88175 -> Prop) (x' : _88175) : (term181 _88175 P x') = (P x').
Proof. exact (@lem3394985 (P x')). Qed.
Lemma lem3394987 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : P x'.
Proof. exact (EQ_MP (@lem3394986 _88175 P x') (@lem3394983 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3394989 {_88162 : Type'} (x : _88162) : x = x.
Proof. exact (@lem21386 _88162 x). Qed.
Lemma lem3394990 {_88162 : Type'} (x : _88162) : x = x.
Proof. exact (@lem3394989 _88162 x). Qed.
Lemma lem3394991 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : (f x') = (f x').
Proof. exact (@lem3394990 _88162 (f x')). Qed.
Lemma lem3394992 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : term178 _88162 _88175 f x'.
Proof. exact (fun h0 : term179 _88162 _88175 f x' => @lem3394991 _88162 _88175 f x'). Qed.
Lemma lem3394994 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3394995 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : (term178 _88162 _88175 f x') = ((f x') = (f x')).
Proof. exact (@lem3394994 ((f x') = (f x'))). Qed.
Lemma lem3394996 {_88162 _88175 : Type'} (f : _88175 -> _88162) (x' : _88175) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3394995 _88162 _88175 f x') (@lem3394992 _88162 _88175 f x')). Qed.
Lemma lem3394998 (a : Prop) (b : Prop) : (term183 a b) = (term184 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3394999 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : (term175 _88162 _88175 P x' f _35735) = (term191 _88162 _88175 P x' f _35735).
Proof. exact (@lem3394998 (P _35735) ((f x') = (f _35735))). Qed.
Lemma lem3395001 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3395002 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : (term191 _88162 _88175 P x' f _35735) = (term192 _88162 _88175 P x' f _35735).
Proof. exact (@lem3395001 (term193 _88162 _88175 P x' f _35735)). Qed.
Lemma lem3395003 {_88162 _88175 : Type'} (P : _88175 -> Prop) (x' : _88175) (f : _88175 -> _88162) (_35735 : _88175) : (term175 _88162 _88175 P x' f _35735) = (term192 _88162 _88175 P x' f _35735).
Proof. exact (TRANS (@lem3394999 _88162 _88175 P x' f _35735) (@lem3395002 _88162 _88175 P x' f _35735)). Qed.
Lemma lem3395005 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term194 _88162 _88175 P f x'.
Proof. exact (conj (@lem3394987 _88162 _88175 x f P x' h1) (@lem3394996 _88162 _88175 f x')). Qed.
Lemma lem3395007 {_88162 _88175 : Type'} (_35735 : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term192 _88162 _88175 P x' f _35735.
Proof. exact (EQ_MP (@lem3395003 _88162 _88175 P x' f _35735) (@lem3394881 _88162 _88175 _35735 x f P x' h1)). Qed.
Lemma lem3395008 {_88162 _88175 : Type'} (_35735 : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term192 _88162 _88175 P x' f _35735.
Proof. exact (@lem3395007 _88162 _88175 _35735 x f P x' h1). Qed.
Lemma lem3395009 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term195 _88162 _88175 P f x'.
Proof. exact (@lem3395008 _88162 _88175 x' x f P x' h1). Qed.
Lemma lem3395012 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : False.
Proof. exact (@lem3395009 _88162 _88175 x f P x' h1 (@lem3395005 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3395013 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : term190.
Proof. exact (fun h0 : ~ False => @lem3395012 _88162 _88175 x f P x' h1). Qed.
Lemma lem3395015 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3395016 : term190 = False.
Proof. exact (@lem3395015 False). Qed.
Lemma lem3395018 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term139 _88162 _88175 x f P x') : False.
Proof. exact (EQ_MP (@lem3395016) (@lem3395013 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3395019 {_88162 _88175 : Type'} (x' : _88175) (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term125 _88162 _88175 x' x f P) : False.
Proof. exact (EQ_MP (@lem3394955) (@lem3394952 _88162 _88175 x' x f P h1)). Qed.
Lemma lem3395020 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term160 _88162 _88175 x f P x') : False.
Proof. exact (or_elim (@lem3394735 _88162 _88175 x f P x' h1) (fun h0 : term125 _88162 _88175 x' x f P => @lem3395019 _88162 _88175 x' x f P h0) (fun h0 : term139 _88162 _88175 x f P x' => @lem3395018 _88162 _88175 x f P x' h0)). Qed.
Lemma lem3395021 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term160 _88162 _88175 x f P x') : (term160 _88162 _88175 x f P x') = False.
Proof. exact (prop_ext (fun h2 : term160 _88162 _88175 x f P x' => @lem3395020 _88162 _88175 x f P x' h1) (fun h2 : False => @lem3394735 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3395022 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (x' : _88175) (h1 : term160 _88162 _88175 x f P x') : False.
Proof. exact (EQ_MP (@lem3395021 _88162 _88175 x f P x' h1) (@lem3394735 _88162 _88175 x f P x' h1)). Qed.
Lemma lem3395023 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term81 _88162 _88175 x f P) : False.
Proof. exact (ex_elim (@lem3394658 _88162 _88175 x f P h1) (fun x' : _88175 => fun h0 : term162 _88162 _88175 x f P x' => @lem3395022 _88162 _88175 x f P x' h0)). Qed.
Lemma lem3395024 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term81 _88162 _88175 x f P) : (term81 _88162 _88175 x f P) = False.
Proof. exact (prop_ext (fun h2 : term81 _88162 _88175 x f P => @lem3395023 _88162 _88175 x f P h1) (fun h2 : False => @lem3394362 _88162 _88175 x f P h1)). Qed.
Lemma lem3395025 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) (h1 : term81 _88162 _88175 x f P) : False.
Proof. exact (EQ_MP (@lem3395024 _88162 _88175 x f P h1) (@lem3394362 _88162 _88175 x f P h1)). Qed.
Lemma lem3395026 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : term80 _88162 _88175 x f P.
Proof. exact (fun h0 : term81 _88162 _88175 x f P => @lem3395025 _88162 _88175 x f P h0). Qed.
Lemma lem3395027 {_88162 _88175 : Type'} (x : _88162) (f : _88175 -> _88162) (P : _88175 -> Prop) : (term49 _88162 _88175 P x f) = (term64 _88162 _88175 x f P).
Proof. exact (EQ_MP (@lem3394361 _88162 _88175 x f P) (@lem3395026 _88162 _88175 x f P)). Qed.
Lemma lem3395032 {_88162 _88175 : Type'} (f : _88175 -> _88162) (P : _88175 -> Prop) : term67 _88162 _88175 f P.
Proof. exact (fun x : _88162 => @lem3395027 _88162 _88175 x f P). Qed.
Lemma lem3395037 {_88162 _88175 : Type'} (f : _88175 -> _88162) : term69 _88162 _88175 f.
Proof. exact (fun P : _88175 -> Prop => @lem3395032 _88162 _88175 f P). Qed.
Lemma lem3395042 {_88162 _88175 : Type'} : term71 _88162 _88175.
Proof. exact (fun f : _88175 -> _88162 => @lem3395037 _88162 _88175 f). Qed.
Lemma lem3395043 {_88162 _88175 : Type'} : term73 _88162 _88175.
Proof. exact (EQ_MP (@lem3394357 _88162 _88175) (@lem3395042 _88162 _88175)). Qed.
Lemma lem3395045 {_88162 _88175 : Type'} : term73 _88162 _88175.
Proof. exact (@lem3394204 _88162 _88175 (@lem3395043 _88162 _88175)). Qed.
Lemma lem3395046 {_88162 _88175 : Type'} (h1 : term74 _88162 _88175) : False.
Proof. exact (@lem3395045 _88162 _88175 (@lem3394188 _88162 _88175 h1)). Qed.
Lemma lem3395047 {_88162 _88175 : Type'} (h1 : term74 _88162 _88175) : (term74 _88162 _88175) = False.
Proof. exact (prop_ext (fun h2 : term74 _88162 _88175 => @lem3395046 _88162 _88175 h1) (fun h2 : False => @lem3394188 _88162 _88175 h1)). Qed.
Lemma lem3395048 {_88162 _88175 : Type'} (h1 : term74 _88162 _88175) : False.
Proof. exact (EQ_MP (@lem3395047 _88162 _88175 h1) (@lem3394188 _88162 _88175 h1)). Qed.
Lemma lem3395049 {_88162 _88175 : Type'} : term73 _88162 _88175.
Proof. exact (fun h0 : term74 _88162 _88175 => @lem3395048 _88162 _88175 h0). Qed.
Lemma lem3395050 {_88162 _88175 : Type'} : term71 _88162 _88175.
Proof. exact (EQ_MP (@lem3394187 _88162 _88175) (@lem3395049 _88162 _88175)). Qed.
Lemma lem3395051 {_88162 _88175 : Type'} : term11 _88162 _88175.
Proof. exact (EQ_MP (@lem3394183 _88162 _88175) (@lem3395050 _88162 _88175)). Qed.
Lemma lem3395052 {_88162 _88175 : Type'} : term10 _88162 _88175.
Proof. exact (EQ_MP (@lem3394048 _88162 _88175) (@lem3395051 _88162 _88175)). Qed.
