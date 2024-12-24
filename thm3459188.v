Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459188_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3459015_spec.
Require Import thm3459016_spec.
Require Import thm3459022_spec.
Require Import thm3459023_spec.
Require Import thm3459028_spec.
Require Import thm3459029_spec.
Lemma lem3459059 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3459029 A s x) (@lem3459028 A s x)). Qed.
Lemma lem3459060 {_89711 : Type'} (s : type686 _89711) (x : _89711) : (term0 _89711 x s) = (term1 _89711 s x).
Proof. exact (@lem3459059 _89711 s x). Qed.
Lemma lem3459061 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term2 _89711 _89725 x P f) = (term3 _89711 _89725 P f x).
Proof. exact (@lem3459060 _89711 (term4 _89711 _89725 P f) x). Qed.
Lemma lem3459071 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term5 _83064 x P) = (term6 _83064 P x).
Proof. exact (EQ_MP (@lem3459023 _83064 P x) (@lem3459022 _83064 P x)). Qed.
Lemma lem3459072 {_89711 : Type'} (P : type909 _89711) (x : _89711 -> Prop) : (term7 _89711 x P) = (term8 _89711 P x).
Proof. exact (@lem3459071 (_89711 -> Prop) P x). Qed.
Lemma lem3459073 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (t : _89711 -> Prop) : (term9 _89711 _89725 t P f) = (term10 _89711 _89725 P f t).
Proof. exact (@lem3459072 _89711 (term11 _89711 _89725 P f) t). Qed.
Lemma lem3459074 {_89711 _89725 : Type'} (GEN_PVAR_55 : _89711 -> Prop) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term12 _89711 _89725 P f GEN_PVAR_55) = (term13 _89711 _89725 GEN_PVAR_55 P f).
Proof. exact (eq_refl (term12 _89711 _89725 P f GEN_PVAR_55)). Qed.
Lemma lem3459075 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term14 _89711 _89725 P f) = (term15 _89711 _89725 P f).
Proof. exact (fun_ext (fun GEN_PVAR_55 : _89711 -> Prop => @lem3459074 _89711 _89725 GEN_PVAR_55 P f)). Qed.
Lemma lem3459076 {_89711 : Type'} : (@GSPEC (_89711 -> Prop)) = (@GSPEC (_89711 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_89711 -> Prop))). Qed.
Lemma lem3459077 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term16 _89711 _89725 P f) = (term4 _89711 _89725 P f).
Proof. exact (MK_COMB (@lem3459076 _89711) (@lem3459075 _89711 _89725 P f)). Qed.
Lemma lem3459078 {_89711 : Type'} (t : _89711 -> Prop) : (@IN (_89711 -> Prop) t) = (@IN (_89711 -> Prop) t).
Proof. exact (eq_refl (@IN (_89711 -> Prop) t)). Qed.
Lemma lem3459079 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term9 _89711 _89725 t P f) = (term17 _89711 _89725 t P f).
Proof. exact (MK_COMB (@lem3459078 _89711 t) (@lem3459077 _89711 _89725 P f)). Qed.
Lemma lem3459080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459081 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term18 _89711 _89725 t P f) = (term19 _89711 _89725 t P f).
Proof. exact (MK_COMB (@lem3459080) (@lem3459079 _89711 _89725 t P f)). Qed.
Lemma lem3459082 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term10 _89711 _89725 P f t) = (term20 _89711 _89725 t P f).
Proof. exact (eq_refl (term10 _89711 _89725 P f t)). Qed.
Lemma lem3459083 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : ((term9 _89711 _89725 t P f) = (term10 _89711 _89725 P f t)) = ((term17 _89711 _89725 t P f) = (term20 _89711 _89725 t P f)).
Proof. exact (MK_COMB (@lem3459081 _89711 _89725 t P f) (@lem3459082 _89711 _89725 t P f)). Qed.
Lemma lem3459084 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term17 _89711 _89725 t P f) = (term20 _89711 _89725 t P f).
Proof. exact (EQ_MP (@lem3459083 _89711 _89725 t P f) (@lem3459073 _89711 _89725 P f t)). Qed.
Lemma lem3459090 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3459091 {_89711 : Type'} (f : type1527 _89711) (y : Prop) : (term22 _89711 f y) = (f y).
Proof. exact (@lem3459090 Prop (type686 _89711) f y). Qed.
Lemma lem3459092 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89725) : (term23 _89711 _89725 t P x) = (term24 _89711 _89725 t P x).
Proof. exact (@lem3459091 _89711 (term25 _89711 t) (P x)). Qed.
Lemma lem3459093 {_89711 : Type'} (p : Prop) (t : _89711 -> Prop) : (term26 _89711 t p) = (term27 _89711 p t).
Proof. exact (eq_refl (term26 _89711 t p)). Qed.
Lemma lem3459094 {_89711 : Type'} (t : _89711 -> Prop) : (term28 _89711 t) = (term25 _89711 t).
Proof. exact (fun_ext (fun p : Prop => @lem3459093 _89711 p t)). Qed.
Lemma lem3459095 {_89725 : Type'} (P : _89725 -> Prop) (x : _89725) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3459096 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89725) : (term23 _89711 _89725 t P x) = (term24 _89711 _89725 t P x).
Proof. exact (MK_COMB (@lem3459094 _89711 t) (@lem3459095 _89725 P x)). Qed.
Lemma lem3459097 {_89711 : Type'} : (@eq ((_89711 -> Prop) -> Prop)) = (@eq ((_89711 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_89711 -> Prop) -> Prop))). Qed.
Lemma lem3459098 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89725) : (term29 _89711 _89725 t P x) = (term30 _89711 _89725 t P x).
Proof. exact (MK_COMB (@lem3459097 _89711) (@lem3459096 _89711 _89725 t P x)). Qed.
Lemma lem3459099 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89725) (t : _89711 -> Prop) : (term24 _89711 _89725 t P x) = (term31 _89711 _89725 P x t).
Proof. exact (eq_refl (term24 _89711 _89725 t P x)). Qed.
Lemma lem3459100 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89725) (t : _89711 -> Prop) : ((term23 _89711 _89725 t P x) = (term24 _89711 _89725 t P x)) = ((term24 _89711 _89725 t P x) = (term31 _89711 _89725 P x t)).
Proof. exact (MK_COMB (@lem3459098 _89711 _89725 t P x) (@lem3459099 _89711 _89725 P x t)). Qed.
Lemma lem3459101 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89725) (t : _89711 -> Prop) : (term24 _89711 _89725 t P x) = (term31 _89711 _89725 P x t).
Proof. exact (EQ_MP (@lem3459100 _89711 _89725 P x t) (@lem3459092 _89711 _89725 t P x)). Qed.
Lemma lem3459106 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) (x : _89725) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3459107 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term32 _89711 _89725 t P f x) = (term33 _89711 _89725 P t f x).
Proof. exact (MK_COMB (@lem3459101 _89711 _89725 P x t) (@lem3459106 _89711 _89725 f x)). Qed.
Lemma lem3459109 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3459110 {_89711 : Type'} (f : type686 _89711) (y : _89711 -> Prop) : (term34 _89711 f y) = (f y).
Proof. exact (@lem3459109 (_89711 -> Prop) Prop f y). Qed.
Lemma lem3459111 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term35 _89711 _89725 P t f x) = (term33 _89711 _89725 P t f x).
Proof. exact (@lem3459110 _89711 (term31 _89711 _89725 P x t) (f x)). Qed.
Lemma lem3459112 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89725) (t : _89711 -> Prop) (t' : _89711 -> Prop) : (term36 _89711 _89725 P x t t') = (term37 _89711 _89725 P x t t').
Proof. exact (eq_refl (term36 _89711 _89725 P x t t')). Qed.
Lemma lem3459113 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89725) (t : _89711 -> Prop) : (term38 _89711 _89725 P x t) = (term31 _89711 _89725 P x t).
Proof. exact (fun_ext (fun t' : _89711 -> Prop => @lem3459112 _89711 _89725 P x t t')). Qed.
Lemma lem3459114 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) (x : _89725) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3459115 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term35 _89711 _89725 P t f x) = (term33 _89711 _89725 P t f x).
Proof. exact (MK_COMB (@lem3459113 _89711 _89725 P x t) (@lem3459114 _89711 _89725 f x)). Qed.
Lemma lem3459116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459117 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term39 _89711 _89725 P t f x) = (term40 _89711 _89725 P t f x).
Proof. exact (MK_COMB (@lem3459116) (@lem3459115 _89711 _89725 P t f x)). Qed.
Lemma lem3459118 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term33 _89711 _89725 P t f x) = (term41 _89711 _89725 P t f x).
Proof. exact (eq_refl (term33 _89711 _89725 P t f x)). Qed.
Lemma lem3459119 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : ((term35 _89711 _89725 P t f x) = (term33 _89711 _89725 P t f x)) = ((term33 _89711 _89725 P t f x) = (term41 _89711 _89725 P t f x)).
Proof. exact (MK_COMB (@lem3459117 _89711 _89725 P t f x) (@lem3459118 _89711 _89725 P t f x)). Qed.
Lemma lem3459120 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term33 _89711 _89725 P t f x) = (term41 _89711 _89725 P t f x).
Proof. exact (EQ_MP (@lem3459119 _89711 _89725 P t f x) (@lem3459111 _89711 _89725 P t f x)). Qed.
Lemma lem3459125 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term32 _89711 _89725 t P f x) = (term41 _89711 _89725 P t f x).
Proof. exact (TRANS (@lem3459107 _89711 _89725 P t f x) (@lem3459120 _89711 _89725 P t f x)). Qed.
Lemma lem3459126 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term42 _89711 _89725 t P f) = (term43 _89711 _89725 P t f).
Proof. exact (fun_ext (fun x : _89725 => @lem3459125 _89711 _89725 P t f x)). Qed.
Lemma lem3459127 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3459128 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term20 _89711 _89725 t P f) = (term44 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459127 _89725) (@lem3459126 _89711 _89725 P t f)). Qed.
Lemma lem3459133 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term17 _89711 _89725 t P f) = (term44 _89711 _89725 P t f).
Proof. exact (TRANS (@lem3459084 _89711 _89725 t P f) (@lem3459128 _89711 _89725 P t f)). Qed.
Lemma lem3459134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3459135 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term45 _89711 _89725 t P f) = (term46 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459134) (@lem3459133 _89711 _89725 P t f)). Qed.
Lemma lem3459136 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (@IN _89711 x t) = (@IN _89711 x t).
Proof. exact (eq_refl (@IN _89711 x t)). Qed.
Lemma lem3459137 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term47 _89711 _89725 P f x t) = (term48 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3459135 _89711 _89725 P t f) (@lem3459136 _89711 x t)). Qed.
Lemma lem3459140 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term49 _89711 _89725 P f x) = (term50 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3459137 _89711 _89725 P f x t)). Qed.
Lemma lem3459141 {_89711 : Type'} : (@all (_89711 -> Prop)) = (@all (_89711 -> Prop)).
Proof. exact (eq_refl (@all (_89711 -> Prop))). Qed.
Lemma lem3459142 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term3 _89711 _89725 P f x) = (term51 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459141 _89711) (@lem3459140 _89711 _89725 P f x)). Qed.
Lemma lem3459147 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term2 _89711 _89725 x P f) = (term51 _89711 _89725 P f x).
Proof. exact (TRANS (@lem3459061 _89711 _89725 P f x) (@lem3459142 _89711 _89725 P f x)). Qed.
Lemma lem3459148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459149 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term52 _89711 _89725 x P f) = (term53 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459148) (@lem3459147 _89711 _89725 P f x)). Qed.
Lemma lem3459151 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term54 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3459016 _83095 p x) (@lem3459015 _83095 p x)). Qed.
Lemma lem3459152 {_89711 : Type'} (p : _89711 -> Prop) (x : _89711) : (term54 _89711 x p) = (p x).
Proof. exact (@lem3459151 _89711 p x). Qed.
Lemma lem3459153 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term55 _89711 _89725 x P f) = (term56 _89711 _89725 P f x).
Proof. exact (@lem3459152 _89711 (term57 _89711 _89725 P f) x). Qed.
Lemma lem3459154 {_89711 _89725 : Type'} (P : _89725 -> Prop) (a : _89711) (f : type1470 _89711 _89725) : (term56 _89711 _89725 P f a) = (term58 _89711 _89725 P a f).
Proof. exact (eq_refl (term56 _89711 _89725 P f a)). Qed.
Lemma lem3459155 {_89711 : Type'} (GEN_PVAR_56 : _89711) : (@SETSPEC _89711 GEN_PVAR_56) = (@SETSPEC _89711 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _89711 GEN_PVAR_56)). Qed.
Lemma lem3459156 {_89711 _89725 : Type'} (GEN_PVAR_56 : _89711) (P : _89725 -> Prop) (a : _89711) (f : type1470 _89711 _89725) : (term59 _89711 _89725 GEN_PVAR_56 P f a) = (term60 _89711 _89725 GEN_PVAR_56 P a f).
Proof. exact (MK_COMB (@lem3459155 _89711 GEN_PVAR_56) (@lem3459154 _89711 _89725 P a f)). Qed.
Lemma lem3459157 {_89711 : Type'} (a : _89711) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3459158 {_89711 _89725 : Type'} (GEN_PVAR_56 : _89711) (P : _89725 -> Prop) (f : type1470 _89711 _89725) (a : _89711) : (term61 _89711 _89725 GEN_PVAR_56 P f a) = (term62 _89711 _89725 GEN_PVAR_56 P f a).
Proof. exact (MK_COMB (@lem3459156 _89711 _89725 GEN_PVAR_56 P a f) (@lem3459157 _89711 a)). Qed.
Lemma lem3459159 {_89711 _89725 : Type'} (GEN_PVAR_56 : _89711) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term63 _89711 _89725 GEN_PVAR_56 P f) = (term64 _89711 _89725 GEN_PVAR_56 P f).
Proof. exact (fun_ext (fun a : _89711 => @lem3459158 _89711 _89725 GEN_PVAR_56 P f a)). Qed.
Lemma lem3459160 {_89711 : Type'} : (@ex _89711) = (@ex _89711).
Proof. exact (eq_refl (@ex _89711)). Qed.
Lemma lem3459161 {_89711 _89725 : Type'} (GEN_PVAR_56 : _89711) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term65 _89711 _89725 GEN_PVAR_56 P f) = (term66 _89711 _89725 GEN_PVAR_56 P f).
Proof. exact (MK_COMB (@lem3459160 _89711) (@lem3459159 _89711 _89725 GEN_PVAR_56 P f)). Qed.
Lemma lem3459162 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term67 _89711 _89725 P f) = (term68 _89711 _89725 P f).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _89711 => @lem3459161 _89711 _89725 GEN_PVAR_56 P f)). Qed.
Lemma lem3459163 {_89711 : Type'} : (@GSPEC _89711) = (@GSPEC _89711).
Proof. exact (eq_refl (@GSPEC _89711)). Qed.
Lemma lem3459164 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term69 _89711 _89725 P f) = (term70 _89711 _89725 P f).
Proof. exact (MK_COMB (@lem3459163 _89711) (@lem3459162 _89711 _89725 P f)). Qed.
Lemma lem3459165 {_89711 : Type'} (x : _89711) : (@IN _89711 x) = (@IN _89711 x).
Proof. exact (eq_refl (@IN _89711 x)). Qed.
Lemma lem3459166 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term55 _89711 _89725 x P f) = (term71 _89711 _89725 x P f).
Proof. exact (MK_COMB (@lem3459165 _89711 x) (@lem3459164 _89711 _89725 P f)). Qed.
Lemma lem3459167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459168 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term72 _89711 _89725 x P f) = (term73 _89711 _89725 x P f).
Proof. exact (MK_COMB (@lem3459167) (@lem3459166 _89711 _89725 x P f)). Qed.
Lemma lem3459169 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term56 _89711 _89725 P f x) = (term58 _89711 _89725 P x f).
Proof. exact (eq_refl (term56 _89711 _89725 P f x)). Qed.
Lemma lem3459170 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term55 _89711 _89725 x P f) = (term56 _89711 _89725 P f x)) = ((term71 _89711 _89725 x P f) = (term58 _89711 _89725 P x f)).
Proof. exact (MK_COMB (@lem3459168 _89711 _89725 x P f) (@lem3459169 _89711 _89725 P x f)). Qed.
Lemma lem3459171 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term71 _89711 _89725 x P f) = (term58 _89711 _89725 P x f).
Proof. exact (EQ_MP (@lem3459170 _89711 _89725 P x f) (@lem3459153 _89711 _89725 P f x)). Qed.
Lemma lem3459178 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term2 _89711 _89725 x P f) = (term71 _89711 _89725 x P f)) = ((term51 _89711 _89725 P f x) = (term58 _89711 _89725 P x f)).
Proof. exact (MK_COMB (@lem3459149 _89711 _89725 P f x) (@lem3459171 _89711 _89725 P x f)). Qed.
Lemma lem3459181 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term74 _89711 _89725 P f) = (term75 _89711 _89725 P f).
Proof. exact (fun_ext (fun x : _89711 => @lem3459178 _89711 _89725 P x f)). Qed.
Lemma lem3459182 {_89711 : Type'} : (@all _89711) = (@all _89711).
Proof. exact (eq_refl (@all _89711)). Qed.
Lemma lem3459183 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term76 _89711 _89725 P f) = (term77 _89711 _89725 P f).
Proof. exact (MK_COMB (@lem3459182 _89711) (@lem3459181 _89711 _89725 P f)). Qed.
Lemma lem3459188 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term77 _89711 _89725 P f) = (term76 _89711 _89725 P f).
Proof. exact (SYM (@lem3459183 _89711 _89725 P f)). Qed.
