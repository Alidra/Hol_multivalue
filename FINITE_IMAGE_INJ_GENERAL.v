Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_INJ_GENERAL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_SUBSET_spec.
Require Import INJECTIVE_ON_LEFT_INVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm7_spec.
Lemma lem3615105 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3615106 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem3615105 A h1 s). Qed.
Lemma lem3615107 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3615108 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem3615107 A s) (@lem3615106 A s h1)). Qed.
Lemma lem3615109 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem3615108 A s h1 t). Qed.
Lemma lem3615110 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem3615111 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem3615110 A t s) (@lem3615109 A s t h1)). Qed.
Lemma lem3615112 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem3615113 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem3615111 A t s h1 (@lem3615112 A s t h2)). Qed.
Lemma lem3615114 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem3615113 A s t h0 h1). Qed.
Lemma lem3615115 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem3615116 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem3615115 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem3615114 A s t h0)). Qed.
Lemma lem3615117 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem3615118 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem3615116 A s h2 (@lem3615117 A h1)). Qed.
Lemma lem3615119 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem3615118 A s h1 h0). Qed.
Lemma lem3615120 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem3615119 A s h1). Qed.
Lemma lem3615121 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem3615120 A h0). Qed.
Lemma lem3615122 {A : Type'} : term10 A.
Proof. exact (@lem3615121 A (@lem3599924 A)). Qed.
Lemma lem3615123 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3615122 A s). Qed.
Lemma lem3615124 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem3615126 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term13 _91401 _91404 f.
Proof. exact (@lem3566182 _91401 _91404 f). Qed.
Lemma lem3615127 {_91401 _91404 : Type'} (f : _91401 -> _91404) : (term13 _91401 _91404 f) = (term14 _91401 _91404 f).
Proof. exact (eq_refl (term13 _91401 _91404 f)). Qed.
Lemma lem3615128 {_91401 _91404 : Type'} (f : _91401 -> _91404) : term14 _91401 _91404 f.
Proof. exact (EQ_MP (@lem3615127 _91401 _91404 f) (@lem3615126 _91401 _91404 f)). Qed.
Lemma lem3615129 {_91401 _91404 : Type'} (f : _91401 -> _91404) (s : _91401 -> Prop) : term15 _91401 _91404 f s.
Proof. exact (@lem3615128 _91401 _91404 f s). Qed.
Lemma lem3615130 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term15 _91401 _91404 f s) = ((term16 _91401 _91404 s f) = (term17 _91401 _91404 s f)).
Proof. exact (eq_refl (term15 _91401 _91404 f s)). Qed.
Lemma lem3615132 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term18 A B s f A') : term18 A B s f A'.
Proof. exact (h1). Qed.
Lemma lem3615133 {B : Type'} (A : B -> Prop) (h1 : @FINITE B A) : @FINITE B A.
Proof. exact (h1). Qed.
Lemma lem3615134 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term16 A B s f) : term16 A B s f.
Proof. exact (h1). Qed.
Lemma lem3615136 {_91401 _91404 : Type'} (s : _91401 -> Prop) (f : _91401 -> _91404) : (term16 _91401 _91404 s f) = (term17 _91401 _91404 s f).
Proof. exact (EQ_MP (@lem3615130 _91401 _91404 s f) (@lem3615129 _91401 _91404 f s)). Qed.
Lemma lem3615137 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term16 A B s f) = (term17 A B s f).
Proof. exact (@lem3615136 A B s f). Qed.
Lemma lem3615138 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term16 A B s f) : term17 A B s f.
Proof. exact (EQ_MP (@lem3615137 A B s f) (@lem3615134 A B s f h1)). Qed.
Lemma lem3615139 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term17 A B s f) : term17 A B s f.
Proof. exact (h1). Qed.
Lemma lem3615140 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (h1 : term19 A B s g f) : term19 A B s g f.
Proof. exact (h1). Qed.
Lemma lem3615142 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem3615124 A s) (@lem3615123 A s)). Qed.
Lemma lem3615143 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (@lem3615142 A s). Qed.
Lemma lem3615144 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : term20 A B s f A'.
Proof. exact (@lem3615143 A (term21 A B s f A')). Qed.
Lemma lem3615145 {A B : Type'} (f : A -> B) : term22 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem3615146 {A B : Type'} (f : A -> B) : (term22 A B f) = (term23 A B f).
Proof. exact (eq_refl (term22 A B f)). Qed.
Lemma lem3615147 {A B : Type'} (f : A -> B) : term23 A B f.
Proof. exact (EQ_MP (@lem3615146 A B f) (@lem3615145 A B f)). Qed.
Lemma lem3615148 {A B : Type'} (f : A -> B) (s : A -> Prop) : term24 A B f s.
Proof. exact (@lem3615147 A B f s). Qed.
Lemma lem3615149 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term24 A B f s) = (term25 A B f s).
Proof. exact (eq_refl (term24 A B f s)). Qed.
Lemma lem3615150 {A B : Type'} (f : A -> B) (s : A -> Prop) : term25 A B f s.
Proof. exact (EQ_MP (@lem3615149 A B f s) (@lem3615148 A B f s)). Qed.
Lemma lem3615151 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3615152 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term26 A B f s.
Proof. exact (@lem3615150 A B f s (@lem3615151 A s h1)). Qed.
Lemma lem3615153 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term26 A B f s) = ((term26 A B f s) = True).
Proof. exact (@lem7 (term26 A B f s)). Qed.
Lemma lem3615154 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term26 A B f s) = True.
Proof. exact (EQ_MP (@lem3615153 A B f s) (@lem3615152 A B f s h1)). Qed.
Lemma lem3615160 {B : Type'} (A : B -> Prop) : (@FINITE B A) = ((@FINITE B A) = True).
Proof. exact (@lem7 (@FINITE B A)). Qed.
Lemma lem3615175 {A B : Type'} (f : A -> B) (s : A -> Prop) : term27 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem3615154 A B f s h0). Qed.
Lemma lem3615176 {A B : Type'} (f : B -> A) (s : B -> Prop) : term28 A B f s.
Proof. exact (@lem3615175 B A f s). Qed.
Lemma lem3615177 {A B : Type'} (g : B -> A) (A' : B -> Prop) : term28 A B g A'.
Proof. exact (@lem3615176 A B g A'). Qed.
Lemma lem3615179 {B : Type'} (A : B -> Prop) (h1 : @FINITE B A) : (@FINITE B A) = True.
Proof. exact (EQ_MP (@lem3615160 B A) (@lem3615133 B A h1)). Qed.
Lemma lem3615180 {B : Type'} (A : B -> Prop) (h1 : @FINITE B A) : True = (@FINITE B A).
Proof. exact (SYM (@lem3615179 B A h1)). Qed.
Lemma lem3615181 {B : Type'} (A : B -> Prop) (h1 : @FINITE B A) : @FINITE B A.
Proof. exact (EQ_MP (@lem3615180 B A h1) (@lem0)). Qed.
Lemma lem3615182 {A B : Type'} (g : B -> A) (A' : B -> Prop) (h1 : @FINITE B A') : (term29 A B g A') = True.
Proof. exact (@lem3615177 A B g A' (@lem3615181 B A' h1)). Qed.
Lemma lem3615183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3615184 {A B : Type'} (g : B -> A) (A' : B -> Prop) (h1 : @FINITE B A') : (term30 A B g A') = (and True).
Proof. exact (MK_COMB (@lem3615183) (@lem3615182 A B g A' h1)). Qed.
Lemma lem3615191 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term31 A B s f g A') = (term31 A B s f g A').
Proof. exact (eq_refl (term31 A B s f g A')). Qed.
Lemma lem3615192 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : @FINITE B A') : (term32 A B s f g A') = (term33 A B s f g A').
Proof. exact (MK_COMB (@lem3615184 A B g A' h1) (@lem3615191 A B s f g A')). Qed.
Lemma lem3615194 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3615195 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term33 A B s f g A') = (term31 A B s f g A').
Proof. exact (@lem3615194 (term31 A B s f g A')). Qed.
Lemma lem3615202 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : @FINITE B A') : (term32 A B s f g A') = (term31 A B s f g A').
Proof. exact (TRANS (@lem3615192 A B s f g A' h1) (@lem3615195 A B s f g A')). Qed.
Lemma lem3615203 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : @FINITE B A') : (term31 A B s f g A') = (term32 A B s f g A').
Proof. exact (SYM (@lem3615202 A B s f g A' h1)). Qed.
Lemma lem3615214 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term19 A B s g f) (h2 : @FINITE B A') : term34 A B s g f A'.
Proof. exact (conj (@lem3615140 A B s g f h1) (@lem3615133 B A' h2)). Qed.
Lemma lem3615230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term35 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3615231 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term35 A s t).
Proof. exact (@lem3615230 A s t). Qed.
Lemma lem3615232 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term31 A B s f g A') = (term36 A B s f g A').
Proof. exact (@lem3615231 A (term21 A B s f A') (@IMAGE B A g A')). Qed.
Lemma lem3615245 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) : (term37 A B s g f A') = (term37 A B s g f A').
Proof. exact (eq_refl (term37 A B s g f A')). Qed.
Lemma lem3615246 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term38 A B s f g A') = (term39 A B s f g A').
Proof. exact (MK_COMB (@lem3615245 A B s g f A') (@lem3615232 A B s f g A')). Qed.
Lemma lem3615249 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term39 A B s f g A') = (term38 A B s f g A').
Proof. exact (SYM (@lem3615246 A B s f g A')). Qed.
Lemma lem3615261 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3615262 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3615261 A P x). Qed.
Lemma lem3615263 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3615262 A s x). Qed.
Lemma lem3615264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3615265 {A : Type'} (s : A -> Prop) (x : A) : (term40 A x s) = (term41 A s x).
Proof. exact (MK_COMB (@lem3615264) (@lem3615263 A s x)). Qed.
Lemma lem3615268 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term42 A B g f x) = x) = ((term42 A B g f x) = x).
Proof. exact (eq_refl ((term42 A B g f x) = x)). Qed.
Lemma lem3615269 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term43 A B s g f x) = (term44 A B s g f x).
Proof. exact (MK_COMB (@lem3615265 A s x) (@lem3615268 A B g f x)). Qed.
Lemma lem3615272 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term45 A B s g f) = (term46 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3615269 A B s g f x)). Qed.
Lemma lem3615273 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3615274 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term19 A B s g f) = (term47 A B s g f).
Proof. exact (MK_COMB (@lem3615273 A) (@lem3615272 A B s g f)). Qed.
Lemma lem3615279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3615280 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term48 A B s g f) = (term49 A B s g f).
Proof. exact (MK_COMB (@lem3615279) (@lem3615274 A B s g f)). Qed.
Lemma lem3615281 {B : Type'} (A : B -> Prop) : (@FINITE B A) = (@FINITE B A).
Proof. exact (eq_refl (@FINITE B A)). Qed.
Lemma lem3615282 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) : (term34 A B s g f A') = (term50 A B s g f A').
Proof. exact (MK_COMB (@lem3615280 A B s g f) (@lem3615281 B A')). Qed.
Lemma lem3615285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3615286 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) : (term37 A B s g f A') = (term51 A B s g f A').
Proof. exact (MK_COMB (@lem3615285) (@lem3615282 A B s g f A')). Qed.
Lemma lem3615294 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term52 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3615295 {A : Type'} (p : A -> Prop) (x : A) : (term52 A x p) = (p x).
Proof. exact (@lem3615294 A p x). Qed.
Lemma lem3615296 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (x : A) : (term53 A B x s f A') = (term54 A B s f A' x).
Proof. exact (@lem3615295 A (term55 A B s f A') x). Qed.
Lemma lem3615297 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (A' : B -> Prop) : (term54 A B s f A' x) = (term56 A B s f x A').
Proof. exact (eq_refl (term54 A B s f A' x)). Qed.
Lemma lem3615298 {A : Type'} (GEN_PVAR_95 : A) : (@SETSPEC A GEN_PVAR_95) = (@SETSPEC A GEN_PVAR_95).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_95)). Qed.
Lemma lem3615299 {A B : Type'} (GEN_PVAR_95 : A) (s : A -> Prop) (f : A -> B) (x : A) (A' : B -> Prop) : (term57 A B GEN_PVAR_95 s f A' x) = (term58 A B GEN_PVAR_95 s f x A').
Proof. exact (MK_COMB (@lem3615298 A GEN_PVAR_95) (@lem3615297 A B s f x A')). Qed.
Lemma lem3615300 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3615301 {A B : Type'} (GEN_PVAR_95 : A) (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (x : A) : (term59 A B GEN_PVAR_95 s f A' x) = (term60 A B GEN_PVAR_95 s f A' x).
Proof. exact (MK_COMB (@lem3615299 A B GEN_PVAR_95 s f x A') (@lem3615300 A x)). Qed.
Lemma lem3615302 {A B : Type'} (GEN_PVAR_95 : A) (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : (term61 A B GEN_PVAR_95 s f A') = (term62 A B GEN_PVAR_95 s f A').
Proof. exact (fun_ext (fun x : A => @lem3615301 A B GEN_PVAR_95 s f A' x)). Qed.
Lemma lem3615303 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3615304 {A B : Type'} (GEN_PVAR_95 : A) (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : (term63 A B GEN_PVAR_95 s f A') = (term64 A B GEN_PVAR_95 s f A').
Proof. exact (MK_COMB (@lem3615303 A) (@lem3615302 A B GEN_PVAR_95 s f A')). Qed.
Lemma lem3615305 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : (term65 A B s f A') = (term66 A B s f A').
Proof. exact (fun_ext (fun GEN_PVAR_95 : A => @lem3615304 A B GEN_PVAR_95 s f A')). Qed.
Lemma lem3615306 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem3615307 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : (term67 A B s f A') = (term21 A B s f A').
Proof. exact (MK_COMB (@lem3615306 A) (@lem3615305 A B s f A')). Qed.
Lemma lem3615308 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3615309 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : (term53 A B x s f A') = (term68 A B x s f A').
Proof. exact (MK_COMB (@lem3615308 A x) (@lem3615307 A B s f A')). Qed.
Lemma lem3615310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3615311 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : (term69 A B x s f A') = (term70 A B x s f A').
Proof. exact (MK_COMB (@lem3615310) (@lem3615309 A B x s f A')). Qed.
Lemma lem3615312 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (A' : B -> Prop) : (term54 A B s f A' x) = (term56 A B s f x A').
Proof. exact (eq_refl (term54 A B s f A' x)). Qed.
Lemma lem3615313 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (A' : B -> Prop) : ((term53 A B x s f A') = (term54 A B s f A' x)) = ((term68 A B x s f A') = (term56 A B s f x A')).
Proof. exact (MK_COMB (@lem3615311 A B x s f A') (@lem3615312 A B s f x A')). Qed.
Lemma lem3615314 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (A' : B -> Prop) : (term68 A B x s f A') = (term56 A B s f x A').
Proof. exact (EQ_MP (@lem3615313 A B s f x A') (@lem3615296 A B s f A' x)). Qed.
Lemma lem3615318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3615319 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3615318 A P x). Qed.
Lemma lem3615320 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3615319 A s x). Qed.
Lemma lem3615321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3615322 {A : Type'} (s : A -> Prop) (x : A) : (term71 A x s) = (term72 A s x).
Proof. exact (MK_COMB (@lem3615321) (@lem3615320 A s x)). Qed.
Lemma lem3615324 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3615325 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3615324 B P x). Qed.
Lemma lem3615326 {A B : Type'} (A' : B -> Prop) (f : A -> B) (x : A) : (term73 A B f x A') = (term74 A B A' f x).
Proof. exact (@lem3615325 B A' (f x)). Qed.
Lemma lem3615327 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) : (term56 A B s f x A') = (term75 A B s A' f x).
Proof. exact (MK_COMB (@lem3615322 A s x) (@lem3615326 A B A' f x)). Qed.
Lemma lem3615330 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) : (term68 A B x s f A') = (term75 A B s A' f x).
Proof. exact (TRANS (@lem3615314 A B s f x A') (@lem3615327 A B s A' f x)). Qed.
Lemma lem3615331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3615332 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) : (term76 A B x s f A') = (term77 A B s A' f x).
Proof. exact (MK_COMB (@lem3615331) (@lem3615330 A B s A' f x)). Qed.
Lemma lem3615334 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term78 A B y f s) = (term79 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3615335 {A B : Type'} (y : A) (f : B -> A) (s : B -> Prop) : (term80 A B y f s) = (term81 A B y f s).
Proof. exact (@lem3615334 B A y f s). Qed.
Lemma lem3615336 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term80 A B x g A') = (term81 A B x g A').
Proof. exact (@lem3615335 A B x g A'). Qed.
Lemma lem3615346 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3615347 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3615346 B P x). Qed.
Lemma lem3615348 {B : Type'} (A : B -> Prop) (x : B) : (@IN B x A) = (A x).
Proof. exact (@lem3615347 B A x). Qed.
Lemma lem3615349 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term82 A B x g x') = (term82 A B x g x').
Proof. exact (eq_refl (term82 A B x g x')). Qed.
Lemma lem3615350 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term83 A B x g x' A') = (term84 A B x g A' x').
Proof. exact (MK_COMB (@lem3615349 A B x g x') (@lem3615348 B A' x')). Qed.
Lemma lem3615353 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term85 A B x g A') = (term86 A B x g A').
Proof. exact (fun_ext (fun x' : B => @lem3615350 A B x g A' x')). Qed.
Lemma lem3615354 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3615355 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term81 A B x g A') = (term87 A B x g A').
Proof. exact (MK_COMB (@lem3615354 B) (@lem3615353 A B x g A')). Qed.
Lemma lem3615360 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term80 A B x g A') = (term87 A B x g A').
Proof. exact (TRANS (@lem3615336 A B x g A') (@lem3615355 A B x g A')). Qed.
Lemma lem3615361 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g : B -> A) (A' : B -> Prop) : (term88 A B s f x g A') = (term89 A B s f x g A').
Proof. exact (MK_COMB (@lem3615332 A B s A' f x) (@lem3615360 A B x g A')). Qed.
Lemma lem3615364 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term90 A B s f g A') = (term91 A B s f g A').
Proof. exact (fun_ext (fun x : A => @lem3615361 A B s f x g A')). Qed.
Lemma lem3615365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3615366 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term36 A B s f g A') = (term92 A B s f g A').
Proof. exact (MK_COMB (@lem3615365 A) (@lem3615364 A B s f g A')). Qed.
Lemma lem3615371 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term39 A B s f g A') = (term93 A B s f g A').
Proof. exact (MK_COMB (@lem3615286 A B s g f A') (@lem3615366 A B s f g A')). Qed.
Lemma lem3615374 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term93 A B s f g A') = (term39 A B s f g A').
Proof. exact (SYM (@lem3615371 A B s f g A')). Qed.
Lemma lem3615376 (p : Prop) : p = (term94 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3615377 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term93 A B s f g A') = (term95 A B s f g A').
Proof. exact (@lem3615376 (term93 A B s f g A')). Qed.
Lemma lem3615378 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term95 A B s f g A') = (term93 A B s f g A').
Proof. exact (SYM (@lem3615377 A B s f g A')). Qed.
Lemma lem3615379 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term96 A B s f g A') : term96 A B s f g A'.
Proof. exact (h1). Qed.
Lemma lem3615382 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term95 A B s f g A') : term95 A B s f g A'.
Proof. exact (h1). Qed.
Lemma lem3615383 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term97 A B s f g A'.
Proof. exact (fun h0 : term95 A B s f g A' => @lem3615382 A B s f g A' h0). Qed.
Lemma lem3615384 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term97 A B s f g A') : term97 A B s f g A'.
Proof. exact (h1). Qed.
Lemma lem3615385 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term95 A B s f g A') : term95 A B s f g A'.
Proof. exact (h1). Qed.
Lemma lem3615386 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term95 A B s f g A') (h2 : term97 A B s f g A') : term95 A B s f g A'.
Proof. exact (@lem3615384 A B s f g A' h2 (@lem3615385 A B s f g A' h1)). Qed.
Lemma lem3615387 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term95 A B s f g A') : term98 A B s f g A'.
Proof. exact (fun h0 : term97 A B s f g A' => @lem3615386 A B s f g A' h1 h0). Qed.
Lemma lem3615388 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term97 A B s f g A') : term97 A B s f g A'.
Proof. exact (h1). Qed.
Lemma lem3615389 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term95 A B s f g A') (h2 : term97 A B s f g A') : term95 A B s f g A'.
Proof. exact (@lem3615387 A B s f g A' h1 (@lem3615388 A B s f g A' h2)). Qed.
Lemma lem3615390 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term97 A B s f g A') : term97 A B s f g A'.
Proof. exact (fun h0 : term95 A B s f g A' => @lem3615389 A B s f g A' h0 h1). Qed.
Lemma lem3615391 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term99 A B s f g A'.
Proof. exact (fun h0 : term97 A B s f g A' => @lem3615390 A B s f g A' h0). Qed.
Lemma lem3615394 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term97 A B s f g A'.
Proof. exact (@lem3615391 A B s f g A' (@lem3615383 A B s f g A')). Qed.
Lemma lem3615395 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term97 A B s f g A'.
Proof. exact (@lem3615394 A B s f g A'). Qed.
Lemma lem3615413 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3615414 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term95 A B s f g A') = (term100 A B s f g A').
Proof. exact (@lem3615413 (term96 A B s f g A')). Qed.
Lemma lem3615416 (t : Prop) : (term101 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3615417 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term100 A B s f g A') = (term93 A B s f g A').
Proof. exact (@lem3615416 (term93 A B s f g A')). Qed.
Lemma lem3615420 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term95 A B s f g A') = (term93 A B s f g A').
Proof. exact (TRANS (@lem3615414 A B s f g A') (@lem3615417 A B s f g A')). Qed.
Lemma lem3615471 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term102 A B f g A') = (term103 A B f g A').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3615420 A B s f g A')). Qed.
Lemma lem3615472 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3615473 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term104 A B f g A') = (term105 A B f g A').
Proof. exact (MK_COMB (@lem3615472 A) (@lem3615471 A B f g A')). Qed.
Lemma lem3615478 {A B : Type'} (g : B -> A) (A' : B -> Prop) : (term106 A B g A') = (term107 A B g A').
Proof. exact (fun_ext (fun f : A -> B => @lem3615473 A B f g A')). Qed.
Lemma lem3615479 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3615480 {A B : Type'} (g : B -> A) (A' : B -> Prop) : (term108 A B g A') = (term109 A B g A').
Proof. exact (MK_COMB (@lem3615479 A B) (@lem3615478 A B g A')). Qed.
Lemma lem3615485 {A B : Type'} (A' : B -> Prop) : (term110 A B A') = (term111 A B A').
Proof. exact (fun_ext (fun g : B -> A => @lem3615480 A B g A')). Qed.
Lemma lem3615486 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3615487 {A B : Type'} (A' : B -> Prop) : (term112 A B A') = (term113 A B A').
Proof. exact (MK_COMB (@lem3615486 A B) (@lem3615485 A B A')). Qed.
Lemma lem3615492 {A B : Type'} : (term114 A B) = (term115 A B).
Proof. exact (fun_ext (fun A' : B -> Prop => @lem3615487 A B A')). Qed.
Lemma lem3615493 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3615502 {A B : Type'} : (term116 A B) = (term117 A B).
Proof. exact (MK_COMB (@lem3615493 B) (@lem3615492 A B)). Qed.
Lemma lem3615507 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term84 A B x g A' x') = (term84 A B x g A' x').
Proof. exact (eq_refl (term84 A B x g A' x')). Qed.
Lemma lem3615508 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term86 A B x g A') = (term86 A B x g A').
Proof. exact (fun_ext (fun x' : B => @lem3615507 A B x g A' x')). Qed.
Lemma lem3615509 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3615510 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term87 A B x g A') = (term87 A B x g A').
Proof. exact (MK_COMB (@lem3615509 B) (@lem3615508 A B x g A')). Qed.
Lemma lem3615517 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) : (term77 A B s A' f x) = (term77 A B s A' f x).
Proof. exact (eq_refl (term77 A B s A' f x)). Qed.
Lemma lem3615518 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g : B -> A) (A' : B -> Prop) : (term89 A B s f x g A') = (term89 A B s f x g A').
Proof. exact (MK_COMB (@lem3615517 A B s A' f x) (@lem3615510 A B x g A')). Qed.
Lemma lem3615519 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term91 A B s f g A') = (term91 A B s f g A').
Proof. exact (fun_ext (fun x : A => @lem3615518 A B s f x g A')). Qed.
Lemma lem3615520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3615521 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term92 A B s f g A') = (term92 A B s f g A').
Proof. exact (MK_COMB (@lem3615520 A) (@lem3615519 A B s f g A')). Qed.
Lemma lem3615522 {B : Type'} (A : B -> Prop) : (@FINITE B A) = (@FINITE B A).
Proof. exact (eq_refl (@FINITE B A)). Qed.
Lemma lem3615527 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term44 A B s g f x) = (term44 A B s g f x).
Proof. exact (eq_refl (term44 A B s g f x)). Qed.
Lemma lem3615528 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term46 A B s g f) = (term46 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3615527 A B s g f x)). Qed.
Lemma lem3615529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3615530 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term47 A B s g f) = (term47 A B s g f).
Proof. exact (MK_COMB (@lem3615529 A) (@lem3615528 A B s g f)). Qed.
Lemma lem3615531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3615532 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term49 A B s g f) = (term49 A B s g f).
Proof. exact (MK_COMB (@lem3615531) (@lem3615530 A B s g f)). Qed.
Lemma lem3615533 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) : (term50 A B s g f A') = (term50 A B s g f A').
Proof. exact (MK_COMB (@lem3615532 A B s g f) (@lem3615522 B A')). Qed.
Lemma lem3615534 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3615535 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) : (term51 A B s g f A') = (term51 A B s g f A').
Proof. exact (MK_COMB (@lem3615534) (@lem3615533 A B s g f A')). Qed.
Lemma lem3615536 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term93 A B s f g A') = (term93 A B s f g A').
Proof. exact (MK_COMB (@lem3615535 A B s g f A') (@lem3615521 A B s f g A')). Qed.
Lemma lem3615537 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term103 A B f g A') = (term103 A B f g A').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3615536 A B s f g A')). Qed.
Lemma lem3615538 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3615539 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term105 A B f g A') = (term105 A B f g A').
Proof. exact (MK_COMB (@lem3615538 A) (@lem3615537 A B f g A')). Qed.
Lemma lem3615540 {A B : Type'} (g : B -> A) (A' : B -> Prop) : (term107 A B g A') = (term107 A B g A').
Proof. exact (fun_ext (fun f : A -> B => @lem3615539 A B f g A')). Qed.
Lemma lem3615541 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3615542 {A B : Type'} (g : B -> A) (A' : B -> Prop) : (term109 A B g A') = (term109 A B g A').
Proof. exact (MK_COMB (@lem3615541 A B) (@lem3615540 A B g A')). Qed.
Lemma lem3615543 {A B : Type'} (A' : B -> Prop) : (term111 A B A') = (term111 A B A').
Proof. exact (fun_ext (fun g : B -> A => @lem3615542 A B g A')). Qed.
Lemma lem3615544 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem3615545 {A B : Type'} (A' : B -> Prop) : (term113 A B A') = (term113 A B A').
Proof. exact (MK_COMB (@lem3615544 A B) (@lem3615543 A B A')). Qed.
Lemma lem3615546 {A B : Type'} : (term115 A B) = (term115 A B).
Proof. exact (fun_ext (fun A' : B -> Prop => @lem3615545 A B A')). Qed.
Lemma lem3615547 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3615548 {A B : Type'} : (term117 A B) = (term117 A B).
Proof. exact (MK_COMB (@lem3615547 B) (@lem3615546 A B)). Qed.
Lemma lem3615605 {A B : Type'} : (term116 A B) = (term117 A B).
Proof. exact (TRANS (@lem3615502 A B) (@lem3615548 A B)). Qed.
Lemma lem3615606 {A B : Type'} : (term117 A B) = (term116 A B).
Proof. exact (SYM (@lem3615605 A B)). Qed.
Lemma lem3615607 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term50 A B s g f A'.
Proof. exact (h1). Qed.
Lemma lem3615610 (p : Prop) : p = (term94 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3615611 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term87 A B x g A') = (term118 A B x g A').
Proof. exact (@lem3615610 (term87 A B x g A')). Qed.
Lemma lem3615612 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term118 A B x g A') = (term87 A B x g A').
Proof. exact (SYM (@lem3615611 A B x g A')). Qed.
Lemma lem3615613 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term119 A B x g A'.
Proof. exact (h1). Qed.
Lemma lem3615620 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term44 A B s g f x) = (term120 A B s g f x).
Proof. exact (@lem17265 (s x) ((term42 A B g f x) = x)). Qed.
Lemma lem3615621 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term46 A B s g f) = (term121 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3615620 A B s g f x)). Qed.
Lemma lem3615622 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3615623 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term47 A B s g f) = (term122 A B s g f).
Proof. exact (MK_COMB (@lem3615622 A) (@lem3615621 A B s g f)). Qed.
Lemma lem3615624 {B : Type'} (A : B -> Prop) : (@FINITE B A) = (@FINITE B A).
Proof. exact (eq_refl (@FINITE B A)). Qed.
Lemma lem3615625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3615626 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term49 A B s g f) = (term123 A B s g f).
Proof. exact (MK_COMB (@lem3615625) (@lem3615623 A B s g f)). Qed.
Lemma lem3615679 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) : (term50 A B s g f A') = (term124 A B s g f A').
Proof. exact (MK_COMB (@lem3615626 A B s g f) (@lem3615624 B A')). Qed.
Lemma lem3615680 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term124 A B s g f A'.
Proof. exact (EQ_MP (@lem3615679 A B s g f A') (@lem3615607 A B s g f A' h1)). Qed.
Lemma lem3615690 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : term75 A B s A' f x.
Proof. exact (h1). Qed.
Lemma lem3615697 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term125 A B x g A' x') = (term126 A B x g A' x').
Proof. exact (@lem17045 (x = (g x')) (A' x')). Qed.
Lemma lem3615698 {B : Type'} (P : B -> Prop) : (term127 B P) = (term128 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3615699 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term119 A B x g A') = (term129 A B x g A').
Proof. exact (@lem3615698 B (term86 A B x g A')). Qed.
Lemma lem3615700 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term130 A B x g A' x') = (term84 A B x g A' x').
Proof. exact (eq_refl (term130 A B x g A' x')). Qed.
Lemma lem3615701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3615702 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term131 A B x g A' x') = (term125 A B x g A' x').
Proof. exact (MK_COMB (@lem3615701) (@lem3615700 A B x g A' x')). Qed.
Lemma lem3615703 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term131 A B x g A' x') = (term126 A B x g A' x').
Proof. exact (TRANS (@lem3615702 A B x g A' x') (@lem3615697 A B x g A' x')). Qed.
Lemma lem3615704 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term132 A B x g A') = (term133 A B x g A').
Proof. exact (fun_ext (fun x' : B => @lem3615703 A B x g A' x')). Qed.
Lemma lem3615705 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3615706 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term129 A B x g A') = (term134 A B x g A').
Proof. exact (MK_COMB (@lem3615705 B) (@lem3615704 A B x g A')). Qed.
Lemma lem3615759 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term119 A B x g A') = (term134 A B x g A').
Proof. exact (TRANS (@lem3615699 A B x g A') (@lem3615706 A B x g A')). Qed.
Lemma lem3615760 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term134 A B x g A'.
Proof. exact (EQ_MP (@lem3615759 A B x g A') (@lem3615613 A B x g A' h1)). Qed.
Lemma lem3615763 {B : Type'} (A : B -> Prop) : (@FINITE B A) = (@FINITE B A).
Proof. exact (eq_refl (@FINITE B A)). Qed.
Lemma lem3615780 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term120 A B s g f x) = (term120 A B s g f x).
Proof. exact (eq_refl (term120 A B s g f x)). Qed.
Lemma lem3615781 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term121 A B s g f) = (term121 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3615780 A B s g f x)). Qed.
Lemma lem3615782 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3615783 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term122 A B s g f) = (term122 A B s g f).
Proof. exact (MK_COMB (@lem3615782 A) (@lem3615781 A B s g f)). Qed.
Lemma lem3615784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3615785 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term123 A B s g f) = (term123 A B s g f).
Proof. exact (MK_COMB (@lem3615784) (@lem3615783 A B s g f)). Qed.
Lemma lem3615786 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) : (term124 A B s g f A') = (term124 A B s g f A').
Proof. exact (MK_COMB (@lem3615785 A B s g f) (@lem3615763 B A')). Qed.
Lemma lem3615787 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term124 A B s g f A'.
Proof. exact (EQ_MP (@lem3615786 A B s g f A') (@lem3615680 A B s g f A' h1)). Qed.
Lemma lem3615794 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3615795 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem3615794 B Prop f x). Qed.
Lemma lem3615797 {A B : Type'} (A' : B -> Prop) (f : A -> B) (x : A) : (term74 A B A' f x) = (term135 A B A' f x).
Proof. exact (@lem3615795 B A' (f x)). Qed.
Lemma lem3615802 {A : Type'} (s : A -> Prop) (x : A) : (term72 A s x) = (term72 A s x).
Proof. exact (eq_refl (term72 A s x)). Qed.
Lemma lem3615803 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) : (term75 A B s A' f x) = (term136 A B s A' f x).
Proof. exact (MK_COMB (@lem3615802 A s x) (@lem3615797 A B A' f x)). Qed.
Lemma lem3615804 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : term136 A B s A' f x.
Proof. exact (EQ_MP (@lem3615803 A B s A' f x) (@lem3615690 A B s A' f x h1)). Qed.
Lemma lem3615805 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3615810 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3615811 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem3615810 B Prop f x). Qed.
Lemma lem3615813 {B : Type'} (A : B -> Prop) (x : B) : (A x) = (@I (B -> Prop) A x).
Proof. exact (@lem3615811 B A x). Qed.
Lemma lem3615814 {B : Type'} (A : B -> Prop) (x : B) : (term137 B A x) = (term138 B A x).
Proof. exact (MK_COMB (@lem3615805) (@lem3615813 B A x)). Qed.
Lemma lem3615825 {A B : Type'} (x : A) (g : B -> A) (x' : B) : (term139 A B x g x') = (term139 A B x g x').
Proof. exact (eq_refl (term139 A B x g x')). Qed.
Lemma lem3615826 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term126 A B x g A' x') = (term140 A B x g A' x').
Proof. exact (MK_COMB (@lem3615825 A B x g x') (@lem3615814 B A' x')). Qed.
Lemma lem3615827 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term133 A B x g A') = (term141 A B x g A').
Proof. exact (fun_ext (fun x' : B => @lem3615826 A B x g A' x')). Qed.
Lemma lem3615828 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3615829 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term134 A B x g A') = (term142 A B x g A').
Proof. exact (MK_COMB (@lem3615828 B) (@lem3615827 A B x g A')). Qed.
Lemma lem3615830 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term142 A B x g A'.
Proof. exact (EQ_MP (@lem3615829 A B x g A') (@lem3615760 A B x g A' h1)). Qed.
Lemma lem3615834 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term122 A B s g f.
Proof. exact (proj1 (@lem3615787 A B s g f A' h1)). Qed.
Lemma lem3615842 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (x' : B) : (term140 A B x g A' x') = (term140 A B x g A' x').
Proof. exact (eq_refl (term140 A B x g A' x')). Qed.
Lemma lem3615843 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term141 A B x g A') = (term141 A B x g A').
Proof. exact (fun_ext (fun x' : B => @lem3615842 A B x g A' x')). Qed.
Lemma lem3615844 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3615846 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) : (term142 A B x g A') = (term142 A B x g A').
Proof. exact (MK_COMB (@lem3615844 B) (@lem3615843 A B x g A')). Qed.
Lemma lem3615847 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term142 A B x g A'.
Proof. exact (EQ_MP (@lem3615846 A B x g A') (@lem3615830 A B x g A' h1)). Qed.
Lemma lem3615863 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term120 A B s g f x) = (term120 A B s g f x).
Proof. exact (eq_refl (term120 A B s g f x)). Qed.
Lemma lem3615864 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term121 A B s g f) = (term121 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3615863 A B s g f x)). Qed.
Lemma lem3615865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3615867 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) : (term122 A B s g f) = (term122 A B s g f).
Proof. exact (MK_COMB (@lem3615865 A) (@lem3615864 A B s g f)). Qed.
Lemma lem3615868 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term122 A B s g f.
Proof. exact (EQ_MP (@lem3615867 A B s g f) (@lem3615834 A B s g f A' h1)). Qed.
Lemma lem3615873 {A B : Type'} (_39272 : B) (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term143 A B x g A' _39272.
Proof. exact (@lem3615847 A B x g A' h1 _39272). Qed.
Lemma lem3615874 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (_39272 : B) : (term143 A B x g A' _39272) = (term140 A B x g A' _39272).
Proof. exact (eq_refl (term143 A B x g A' _39272)). Qed.
Lemma lem3615876 {A B : Type'} (_39273 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term144 A B s g f _39273.
Proof. exact (@lem3615868 A B s g f A' h1 _39273). Qed.
Lemma lem3615877 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39273 : A) : (term144 A B s g f _39273) = (term120 A B s g f _39273).
Proof. exact (eq_refl (term144 A B s g f _39273)). Qed.
Lemma lem3615884 {A B : Type'} (_39272 : B) (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term140 A B x g A' _39272.
Proof. exact (EQ_MP (@lem3615874 A B x g A' _39272) (@lem3615873 A B _39272 x g A' h1)). Qed.
Lemma lem3615894 {A B : Type'} (_39273 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term120 A B s g f _39273.
Proof. exact (EQ_MP (@lem3615877 A B s g f _39273) (@lem3615876 A B _39273 s g f A' h1)). Qed.
Lemma lem3615957 {A : Type'} (x : A) (y : A) (z : A) : term145 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem3615963 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : s x.
Proof. exact (proj1 (@lem3615804 A B s A' f x h1)). Qed.
Lemma lem3615964 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : term146 A s x.
Proof. exact (fun h0 : term137 A s x => @lem3615963 A B s A' f x h1). Qed.
Lemma lem3615966 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3615967 {A : Type'} (s : A -> Prop) (x : A) : (term146 A s x) = (s x).
Proof. exact (@lem3615966 (s x)). Qed.
Lemma lem3615968 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : s x.
Proof. exact (EQ_MP (@lem3615967 A s x) (@lem3615964 A B s A' f x h1)). Qed.
Lemma lem3615974 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3615975 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : (term120 A B s g f _39273) = (term148 A B g f s _39273).
Proof. exact (@lem3615974 ((term42 A B g f _39273) = _39273) (term137 A s _39273)). Qed.
Lemma lem3615983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3615984 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : (term149 A B s g f _39273) = (term150 A B g f s _39273).
Proof. exact (MK_COMB (@lem3615983) (@lem3615975 A B g f s _39273)). Qed.
Lemma lem3615992 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : (term148 A B g f s _39273) = (term148 A B g f s _39273).
Proof. exact (eq_refl (term148 A B g f s _39273)). Qed.
Lemma lem3615993 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : ((term120 A B s g f _39273) = (term148 A B g f s _39273)) = ((term148 A B g f s _39273) = (term148 A B g f s _39273)).
Proof. exact (MK_COMB (@lem3615984 A B g f s _39273) (@lem3615992 A B g f s _39273)). Qed.
Lemma lem3615995 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3615996 (x : Prop) : (x = x) = True.
Proof. exact (@lem3615995 Prop x). Qed.
Lemma lem3615997 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : ((term148 A B g f s _39273) = (term148 A B g f s _39273)) = True.
Proof. exact (@lem3615996 (term148 A B g f s _39273)). Qed.
Lemma lem3615998 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : ((term120 A B s g f _39273) = (term148 A B g f s _39273)) = True.
Proof. exact (TRANS (@lem3615993 A B g f s _39273) (@lem3615997 A B g f s _39273)). Qed.
Lemma lem3615999 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : True = ((term120 A B s g f _39273) = (term148 A B g f s _39273)).
Proof. exact (SYM (@lem3615998 A B g f s _39273)). Qed.
Lemma lem3616000 {A B : Type'} (g : B -> A) (f : A -> B) (s : A -> Prop) (_39273 : A) : (term120 A B s g f _39273) = (term148 A B g f s _39273).
Proof. exact (EQ_MP (@lem3615999 A B g f s _39273) (@lem0)). Qed.
Lemma lem3616001 {A B : Type'} (_39273 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term148 A B g f s _39273.
Proof. exact (EQ_MP (@lem3616000 A B g f s _39273) (@lem3615894 A B _39273 s g f A' h1)). Qed.
Lemma lem3616003 (b : Prop) (a : Prop) : (a \/ b) = (term151 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3616004 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39273 : A) : (term148 A B g f s _39273) = (term152 A B s g f _39273).
Proof. exact (@lem3616003 (term137 A s _39273) ((term42 A B g f _39273) = _39273)). Qed.
Lemma lem3616006 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3616007 {A : Type'} (s : A -> Prop) (_39273 : A) : (term153 A s _39273) = (s _39273).
Proof. exact (@lem3616006 (s _39273)). Qed.
Lemma lem3616008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3616009 {A : Type'} (s : A -> Prop) (_39273 : A) : (term154 A s _39273) = (term41 A s _39273).
Proof. exact (MK_COMB (@lem3616008) (@lem3616007 A s _39273)). Qed.
Lemma lem3616010 {A B : Type'} (g : B -> A) (f : A -> B) (_39273 : A) : ((term42 A B g f _39273) = _39273) = ((term42 A B g f _39273) = _39273).
Proof. exact (eq_refl ((term42 A B g f _39273) = _39273)). Qed.
Lemma lem3616011 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39273 : A) : (term152 A B s g f _39273) = (term44 A B s g f _39273).
Proof. exact (MK_COMB (@lem3616009 A s _39273) (@lem3616010 A B g f _39273)). Qed.
Lemma lem3616012 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_39273 : A) : (term148 A B g f s _39273) = (term44 A B s g f _39273).
Proof. exact (TRANS (@lem3616004 A B s g f _39273) (@lem3616011 A B s g f _39273)). Qed.
Lemma lem3616015 {A B : Type'} (_39273 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term44 A B s g f _39273.
Proof. exact (EQ_MP (@lem3616012 A B s g f _39273) (@lem3616001 A B _39273 s g f A' h1)). Qed.
Lemma lem3616016 {A B : Type'} (_39273 : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term44 A B s g f _39273.
Proof. exact (@lem3616015 A B _39273 s g f A' h1). Qed.
Lemma lem3616017 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term44 A B s g f x.
Proof. exact (@lem3616016 A B x s g f A' h1). Qed.
Lemma lem3616020 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : (term42 A B g f x) = x.
Proof. exact (@lem3616017 A B x s g f A' h1 (@lem3615968 A B s A' f x h2)). Qed.
Lemma lem3616021 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : term155 A B g f x.
Proof. exact (fun h0 : term156 A B g f x => @lem3616020 A B g s A' f x h1 h2). Qed.
Lemma lem3616023 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3616024 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term155 A B g f x) = ((term42 A B g f x) = x).
Proof. exact (@lem3616023 ((term42 A B g f x) = x)). Qed.
Lemma lem3616025 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : (term42 A B g f x) = x.
Proof. exact (EQ_MP (@lem3616024 A B g f x) (@lem3616021 A B g s A' f x h1 h2)). Qed.
Lemma lem3616027 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3616028 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3616027 A x). Qed.
Lemma lem3616029 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term42 A B g f x) = (term42 A B g f x).
Proof. exact (@lem3616028 A (term42 A B g f x)). Qed.
Lemma lem3616030 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : term157 A B g f x.
Proof. exact (fun h0 : term158 A B g f x => @lem3616029 A B g f x). Qed.
Lemma lem3616032 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3616033 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term157 A B g f x) = ((term42 A B g f x) = (term42 A B g f x)).
Proof. exact (@lem3616032 ((term42 A B g f x) = (term42 A B g f x))). Qed.
Lemma lem3616034 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term42 A B g f x) = (term42 A B g f x).
Proof. exact (EQ_MP (@lem3616033 A B g f x) (@lem3616030 A B g f x)). Qed.
Lemma lem3616052 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3616053 {A : Type'} (y : A) (x : A) (z : A) : (term159 A x y z) = (term160 A y x z).
Proof. exact (@lem3616052 (y = z) (term161 A x z)). Qed.
Lemma lem3616063 {A : Type'} (x : A) (y : A) : (term162 A x y) = (term162 A x y).
Proof. exact (eq_refl (term162 A x y)). Qed.
Lemma lem3616064 {A : Type'} (y : A) (x : A) (z : A) : (term145 A x y z) = (term163 A y x z).
Proof. exact (MK_COMB (@lem3616063 A x y) (@lem3616053 A y x z)). Qed.
Lemma lem3616068 (q : Prop) (p : Prop) (r : Prop) : (term164 p q r) = (term164 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3616069 {A : Type'} (y : A) (x : A) (z : A) : (term163 A y x z) = (term165 A y x z).
Proof. exact (@lem3616068 (y = z) (term161 A x y) (term161 A x z)). Qed.
Lemma lem3616091 {A : Type'} (y : A) (x : A) (z : A) : (term145 A x y z) = (term165 A y x z).
Proof. exact (TRANS (@lem3616064 A y x z) (@lem3616069 A y x z)). Qed.
Lemma lem3616092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3616093 {A : Type'} (y : A) (x : A) (z : A) : (term166 A x y z) = (term167 A y x z).
Proof. exact (MK_COMB (@lem3616092) (@lem3616091 A y x z)). Qed.
Lemma lem3616115 {A : Type'} (y : A) (x : A) (z : A) : (term165 A y x z) = (term165 A y x z).
Proof. exact (eq_refl (term165 A y x z)). Qed.
Lemma lem3616116 {A : Type'} (y : A) (x : A) (z : A) : ((term145 A x y z) = (term165 A y x z)) = ((term165 A y x z) = (term165 A y x z)).
Proof. exact (MK_COMB (@lem3616093 A y x z) (@lem3616115 A y x z)). Qed.
Lemma lem3616118 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3616119 (x : Prop) : (x = x) = True.
Proof. exact (@lem3616118 Prop x). Qed.
Lemma lem3616120 {A : Type'} (y : A) (x : A) (z : A) : ((term165 A y x z) = (term165 A y x z)) = True.
Proof. exact (@lem3616119 (term165 A y x z)). Qed.
Lemma lem3616121 {A : Type'} (y : A) (x : A) (z : A) : ((term145 A x y z) = (term165 A y x z)) = True.
Proof. exact (TRANS (@lem3616116 A y x z) (@lem3616120 A y x z)). Qed.
Lemma lem3616122 {A : Type'} (y : A) (x : A) (z : A) : True = ((term145 A x y z) = (term165 A y x z)).
Proof. exact (SYM (@lem3616121 A y x z)). Qed.
Lemma lem3616123 {A : Type'} (y : A) (x : A) (z : A) : (term145 A x y z) = (term165 A y x z).
Proof. exact (EQ_MP (@lem3616122 A y x z) (@lem0)). Qed.
Lemma lem3616124 {A : Type'} (y : A) (x : A) (z : A) : term165 A y x z.
Proof. exact (EQ_MP (@lem3616123 A y x z) (@lem3615957 A x y z)). Qed.
Lemma lem3616126 (b : Prop) (a : Prop) : (a \/ b) = (term151 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3616127 {A : Type'} (x : A) (y : A) (z : A) : (term165 A y x z) = (term168 A x y z).
Proof. exact (@lem3616126 (term169 A y x z) (y = z)). Qed.
Lemma lem3616129 (a : Prop) (b : Prop) : (term170 a b) = (term171 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3616130 {A : Type'} (y : A) (x : A) (z : A) : (term172 A y x z) = (term173 A y x z).
Proof. exact (@lem3616129 (term161 A x y) (term161 A x z)). Qed.
Lemma lem3616132 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3616133 {A : Type'} (x : A) (y : A) : (term174 A x y) = (x = y).
Proof. exact (@lem3616132 (x = y)). Qed.
Lemma lem3616134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3616135 {A : Type'} (x : A) (y : A) : (term175 A x y) = (term176 A x y).
Proof. exact (MK_COMB (@lem3616134) (@lem3616133 A x y)). Qed.
Lemma lem3616137 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3616138 {A : Type'} (x : A) (z : A) : (term174 A x z) = (x = z).
Proof. exact (@lem3616137 (x = z)). Qed.
Lemma lem3616139 {A : Type'} (y : A) (x : A) (z : A) : (term173 A y x z) = (term177 A y x z).
Proof. exact (MK_COMB (@lem3616135 A x y) (@lem3616138 A x z)). Qed.
Lemma lem3616140 {A : Type'} (y : A) (x : A) (z : A) : (term172 A y x z) = (term177 A y x z).
Proof. exact (TRANS (@lem3616130 A y x z) (@lem3616139 A y x z)). Qed.
Lemma lem3616141 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3616142 {A : Type'} (y : A) (x : A) (z : A) : (term178 A y x z) = (term179 A y x z).
Proof. exact (MK_COMB (@lem3616141) (@lem3616140 A y x z)). Qed.
Lemma lem3616143 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3616144 {A : Type'} (x : A) (y : A) (z : A) : (term168 A x y z) = (term180 A x y z).
Proof. exact (MK_COMB (@lem3616142 A y x z) (@lem3616143 A y z)). Qed.
Lemma lem3616145 {A : Type'} (x : A) (y : A) (z : A) : (term165 A y x z) = (term180 A x y z).
Proof. exact (TRANS (@lem3616127 A x y z) (@lem3616144 A x y z)). Qed.
Lemma lem3616147 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : term181 A B g f x.
Proof. exact (conj (@lem3616025 A B g s A' f x h1 h2) (@lem3616034 A B g f x)). Qed.
Lemma lem3616149 {A : Type'} (x : A) (y : A) (z : A) : term180 A x y z.
Proof. exact (EQ_MP (@lem3616145 A x y z) (@lem3616124 A y x z)). Qed.
Lemma lem3616150 {A : Type'} (x : A) (y : A) (z : A) : term180 A x y z.
Proof. exact (@lem3616149 A x y z). Qed.
Lemma lem3616151 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : term182 A B g f x.
Proof. exact (@lem3616150 A (term42 A B g f x) x (term42 A B g f x)). Qed.
Lemma lem3616154 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : x = (term42 A B g f x).
Proof. exact (@lem3616151 A B g f x (@lem3616147 A B g s A' f x h1 h2)). Qed.
Lemma lem3616155 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : term183 A B g f x.
Proof. exact (fun h0 : term184 A B g f x => @lem3616154 A B g s A' f x h1 h2). Qed.
Lemma lem3616157 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3616158 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term183 A B g f x) = (x = (term42 A B g f x)).
Proof. exact (@lem3616157 (x = (term42 A B g f x))). Qed.
Lemma lem3616159 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : x = (term42 A B g f x).
Proof. exact (EQ_MP (@lem3616158 A B g f x) (@lem3616155 A B g s A' f x h1 h2)). Qed.
Lemma lem3616161 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : term135 A B A' f x.
Proof. exact (proj2 (@lem3615804 A B s A' f x h1)). Qed.
Lemma lem3616162 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : term185 A B A' f x.
Proof. exact (fun h0 : term186 A B A' f x => @lem3616161 A B s A' f x h1). Qed.
Lemma lem3616164 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3616165 {A B : Type'} (A' : B -> Prop) (f : A -> B) (x : A) : (term185 A B A' f x) = (term135 A B A' f x).
Proof. exact (@lem3616164 (term135 A B A' f x)). Qed.
Lemma lem3616166 {A B : Type'} (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term75 A B s A' f x) : term135 A B A' f x.
Proof. exact (EQ_MP (@lem3616165 A B A' f x) (@lem3616162 A B s A' f x h1)). Qed.
Lemma lem3616168 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3616169 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (_39272 : B) : (term140 A B x g A' _39272) = (term189 A B x g A' _39272).
Proof. exact (@lem3616168 (x = (g _39272)) (@I (B -> Prop) A' _39272)). Qed.
Lemma lem3616171 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3616172 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (_39272 : B) : (term189 A B x g A' _39272) = (term190 A B x g A' _39272).
Proof. exact (@lem3616171 (term191 A B x g A' _39272)). Qed.
Lemma lem3616173 {A B : Type'} (x : A) (g : B -> A) (A' : B -> Prop) (_39272 : B) : (term140 A B x g A' _39272) = (term190 A B x g A' _39272).
Proof. exact (TRANS (@lem3616169 A B x g A' _39272) (@lem3616172 A B x g A' _39272)). Qed.
Lemma lem3616175 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : term192 A B g A' f x.
Proof. exact (conj (@lem3616159 A B g s A' f x h1 h2) (@lem3616166 A B s A' f x h2)). Qed.
Lemma lem3616177 {A B : Type'} (_39272 : B) (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term190 A B x g A' _39272.
Proof. exact (EQ_MP (@lem3616173 A B x g A' _39272) (@lem3615884 A B _39272 x g A' h1)). Qed.
Lemma lem3616178 {A B : Type'} (_39272 : B) (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term190 A B x g A' _39272.
Proof. exact (@lem3616177 A B _39272 x g A' h1). Qed.
Lemma lem3616179 {A B : Type'} (f : A -> B) (x : A) (g : B -> A) (A' : B -> Prop) (h1 : term119 A B x g A') : term193 A B g A' f x.
Proof. exact (@lem3616178 A B (f x) x g A' h1). Qed.
Lemma lem3616182 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term119 A B x g A') (h2 : term50 A B s g f A') (h3 : term75 A B s A' f x) : False.
Proof. exact (@lem3616179 A B f x g A' h1 (@lem3616175 A B g s A' f x h2 h3)). Qed.
Lemma lem3616183 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term119 A B x g A') (h2 : term50 A B s g f A') (h3 : term75 A B s A' f x) : term194.
Proof. exact (fun h0 : ~ False => @lem3616182 A B g s A' f x h1 h2 h3). Qed.
Lemma lem3616185 (p : Prop) : (term147 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3616186 : term194 = False.
Proof. exact (@lem3616185 False). Qed.
Lemma lem3616187 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term119 A B x g A') (h2 : term50 A B s g f A') (h3 : term75 A B s A' f x) : False.
Proof. exact (EQ_MP (@lem3616186) (@lem3616183 A B g s A' f x h1 h2 h3)). Qed.
Lemma lem3616188 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term119 A B x g A') (h2 : term50 A B s g f A') (h3 : term75 A B s A' f x) : (term75 A B s A' f x) = False.
Proof. exact (prop_ext (fun h4 : term75 A B s A' f x => @lem3616187 A B g s A' f x h1 h2 h3) (fun h4 : False => @lem3615690 A B s A' f x h3)). Qed.
Lemma lem3616189 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term119 A B x g A') (h2 : term50 A B s g f A') (h3 : term75 A B s A' f x) : False.
Proof. exact (EQ_MP (@lem3616188 A B g s A' f x h1 h2 h3) (@lem3615690 A B s A' f x h3)). Qed.
Lemma lem3616190 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term119 A B x g A') (h2 : term50 A B s g f A') (h3 : term75 A B s A' f x) : (term119 A B x g A') = False.
Proof. exact (prop_ext (fun h4 : term119 A B x g A' => @lem3616189 A B g s A' f x h1 h2 h3) (fun h4 : False => @lem3615613 A B x g A' h1)). Qed.
Lemma lem3616191 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term119 A B x g A') (h2 : term50 A B s g f A') (h3 : term75 A B s A' f x) : False.
Proof. exact (EQ_MP (@lem3616190 A B g s A' f x h1 h2 h3) (@lem3615613 A B x g A' h1)). Qed.
Lemma lem3616192 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : term118 A B x g A'.
Proof. exact (fun h0 : term119 A B x g A' => @lem3616191 A B g s A' f x h0 h1 h2). Qed.
Lemma lem3616193 {A B : Type'} (g : B -> A) (s : A -> Prop) (A' : B -> Prop) (f : A -> B) (x : A) (h1 : term50 A B s g f A') (h2 : term75 A B s A' f x) : term87 A B x g A'.
Proof. exact (EQ_MP (@lem3615612 A B x g A') (@lem3616192 A B g s A' f x h1 h2)). Qed.
Lemma lem3616194 {A B : Type'} (x : A) (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term89 A B s f x g A'.
Proof. exact (fun h0 : term75 A B s A' f x => @lem3616193 A B g s A' f x h1 h0). Qed.
Lemma lem3616199 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term50 A B s g f A') : term92 A B s f g A'.
Proof. exact (fun x : A => @lem3616194 A B x s g f A' h1). Qed.
Lemma lem3616200 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term93 A B s f g A'.
Proof. exact (fun h0 : term50 A B s g f A' => @lem3616199 A B s g f A' h0). Qed.
Lemma lem3616205 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) : term105 A B f g A'.
Proof. exact (fun s : A -> Prop => @lem3616200 A B s f g A'). Qed.
Lemma lem3616210 {A B : Type'} (g : B -> A) (A' : B -> Prop) : term109 A B g A'.
Proof. exact (fun f : A -> B => @lem3616205 A B f g A'). Qed.
Lemma lem3616215 {A B : Type'} (A' : B -> Prop) : term113 A B A'.
Proof. exact (fun g : B -> A => @lem3616210 A B g A'). Qed.
Lemma lem3616220 {A B : Type'} : term117 A B.
Proof. exact (fun A' : B -> Prop => @lem3616215 A B A'). Qed.
Lemma lem3616221 {A B : Type'} : term116 A B.
Proof. exact (EQ_MP (@lem3615606 A B) (@lem3616220 A B)). Qed.
Lemma lem3616222 {A B : Type'} (A' : B -> Prop) : term195 A B A'.
Proof. exact (@lem3616221 A B A'). Qed.
Lemma lem3616223 {A B : Type'} (A' : B -> Prop) : (term195 A B A') = (term112 A B A').
Proof. exact (eq_refl (term195 A B A')). Qed.
Lemma lem3616224 {A B : Type'} (A' : B -> Prop) : term112 A B A'.
Proof. exact (EQ_MP (@lem3616223 A B A') (@lem3616222 A B A')). Qed.
Lemma lem3616225 {A B : Type'} (A' : B -> Prop) (g : B -> A) : term196 A B A' g.
Proof. exact (@lem3616224 A B A' g). Qed.
Lemma lem3616226 {A B : Type'} (g : B -> A) (A' : B -> Prop) : (term196 A B A' g) = (term108 A B g A').
Proof. exact (eq_refl (term196 A B A' g)). Qed.
Lemma lem3616227 {A B : Type'} (g : B -> A) (A' : B -> Prop) : term108 A B g A'.
Proof. exact (EQ_MP (@lem3616226 A B g A') (@lem3616225 A B A' g)). Qed.
Lemma lem3616228 {A B : Type'} (g : B -> A) (A' : B -> Prop) (f : A -> B) : term197 A B g A' f.
Proof. exact (@lem3616227 A B g A' f). Qed.
Lemma lem3616229 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term197 A B g A' f) = (term104 A B f g A').
Proof. exact (eq_refl (term197 A B g A' f)). Qed.
Lemma lem3616230 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) : term104 A B f g A'.
Proof. exact (EQ_MP (@lem3616229 A B f g A') (@lem3616228 A B g A' f)). Qed.
Lemma lem3616231 {A B : Type'} (f : A -> B) (g : B -> A) (A' : B -> Prop) (s : A -> Prop) : term198 A B f g A' s.
Proof. exact (@lem3616230 A B f g A' s). Qed.
Lemma lem3616232 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : (term198 A B f g A' s) = (term95 A B s f g A').
Proof. exact (eq_refl (term198 A B f g A' s)). Qed.
Lemma lem3616233 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term95 A B s f g A'.
Proof. exact (EQ_MP (@lem3616232 A B s f g A') (@lem3616231 A B f g A' s)). Qed.
Lemma lem3616235 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term95 A B s f g A'.
Proof. exact (@lem3615395 A B s f g A' (@lem3616233 A B s f g A')). Qed.
Lemma lem3616236 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term96 A B s f g A') : False.
Proof. exact (@lem3616235 A B s f g A' (@lem3615379 A B s f g A' h1)). Qed.
Lemma lem3616237 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term96 A B s f g A') : (term96 A B s f g A') = False.
Proof. exact (prop_ext (fun h2 : term96 A B s f g A' => @lem3616236 A B s f g A' h1) (fun h2 : False => @lem3615379 A B s f g A' h1)). Qed.
Lemma lem3616238 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) (h1 : term96 A B s f g A') : False.
Proof. exact (EQ_MP (@lem3616237 A B s f g A' h1) (@lem3615379 A B s f g A' h1)). Qed.
Lemma lem3616239 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term95 A B s f g A'.
Proof. exact (fun h0 : term96 A B s f g A' => @lem3616238 A B s f g A' h0). Qed.
Lemma lem3616240 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term93 A B s f g A'.
Proof. exact (EQ_MP (@lem3615378 A B s f g A') (@lem3616239 A B s f g A')). Qed.
Lemma lem3616241 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term39 A B s f g A'.
Proof. exact (EQ_MP (@lem3615374 A B s f g A') (@lem3616240 A B s f g A')). Qed.
Lemma lem3616242 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (A' : B -> Prop) : term38 A B s f g A'.
Proof. exact (EQ_MP (@lem3615249 A B s f g A') (@lem3616241 A B s f g A')). Qed.
Lemma lem3616243 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term19 A B s g f) (h2 : @FINITE B A') : term31 A B s f g A'.
Proof. exact (@lem3616242 A B s f g A' (@lem3615214 A B s g f A' h1 h2)). Qed.
Lemma lem3616244 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term19 A B s g f) (h2 : @FINITE B A') : term32 A B s f g A'.
Proof. exact (EQ_MP (@lem3615203 A B s f g A' h2) (@lem3616243 A B s g f A' h1 h2)). Qed.
Lemma lem3616245 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term19 A B s g f) (h2 : @FINITE B A') : term199 A B s f A'.
Proof. exact (ex_intro (term200 A B s f A') (@IMAGE B A g A') (@lem3616244 A B s g f A' h1 h2)). Qed.
Lemma lem3616246 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (A' : B -> Prop) (h1 : term19 A B s g f) (h2 : @FINITE B A') : term201 A B s f A'.
Proof. exact (@lem3615144 A B s f A' (@lem3616245 A B s g f A' h1 h2)). Qed.
Lemma lem3616247 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term17 A B s f) (h2 : @FINITE B A') : term201 A B s f A'.
Proof. exact (ex_elim (@lem3615139 A B s f h1) (fun g : B -> A => fun h0 : term202 A B s f g => @lem3616246 A B s g f A' h0 h2)). Qed.
Lemma lem3616248 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : @FINITE B A') : term203 A B s f A'.
Proof. exact (fun h0 : term17 A B s f => @lem3616247 A B s f A' h0 h1). Qed.
Lemma lem3616249 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term16 A B s f) (h2 : @FINITE B A') : term201 A B s f A'.
Proof. exact (@lem3616248 A B s f A' h2 (@lem3615138 A B s f h1)). Qed.
Lemma lem3616250 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term18 A B s f A') : @FINITE B A'.
Proof. exact (proj2 (@lem3615132 A B s f A' h1)). Qed.
Lemma lem3616251 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term18 A B s f A') : term16 A B s f.
Proof. exact (proj1 (@lem3615132 A B s f A' h1)). Qed.
Lemma lem3616252 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term16 A B s f) (h2 : @FINITE B A') : (@FINITE B A') = (term201 A B s f A').
Proof. exact (prop_ext (fun h3 : @FINITE B A' => @lem3616249 A B s f A' h1 h2) (fun h3 : term201 A B s f A' => @lem3615133 B A' h2)). Qed.
Lemma lem3616253 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term16 A B s f) (h2 : @FINITE B A') : term201 A B s f A'.
Proof. exact (EQ_MP (@lem3616252 A B s f A' h1 h2) (@lem3615133 B A' h2)). Qed.
Lemma lem3616254 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term16 A B s f) (h2 : @FINITE B A') : (term16 A B s f) = (term201 A B s f A').
Proof. exact (prop_ext (fun h3 : term16 A B s f => @lem3616253 A B s f A' h1 h2) (fun h3 : term201 A B s f A' => @lem3615134 A B s f h1)). Qed.
Lemma lem3616255 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term16 A B s f) (h2 : @FINITE B A') : term201 A B s f A'.
Proof. exact (EQ_MP (@lem3616254 A B s f A' h1 h2) (@lem3615134 A B s f h1)). Qed.
Lemma lem3616256 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term16 A B s f) (h2 : term18 A B s f A') : (@FINITE B A') = (term201 A B s f A').
Proof. exact (prop_ext (fun h3 : @FINITE B A' => @lem3616255 A B s f A' h1 h3) (fun h3 : term201 A B s f A' => @lem3616250 A B s f A' h2)). Qed.
Lemma lem3616257 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term16 A B s f) (h2 : term18 A B s f A') : term201 A B s f A'.
Proof. exact (EQ_MP (@lem3616256 A B s f A' h1 h2) (@lem3616250 A B s f A' h2)). Qed.
Lemma lem3616258 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term18 A B s f A') : (term16 A B s f) = (term201 A B s f A').
Proof. exact (prop_ext (fun h2 : term16 A B s f => @lem3616257 A B s f A' h2 h1) (fun h2 : term201 A B s f A' => @lem3616251 A B s f A' h1)). Qed.
Lemma lem3616259 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) (h1 : term18 A B s f A') : term201 A B s f A'.
Proof. exact (EQ_MP (@lem3616258 A B s f A' h1) (@lem3616251 A B s f A' h1)). Qed.
Lemma lem3616260 {A B : Type'} (s : A -> Prop) (f : A -> B) (A' : B -> Prop) : term204 A B s f A'.
Proof. exact (fun h0 : term18 A B s f A' => @lem3616259 A B s f A' h0). Qed.
Lemma lem3616265 {A B : Type'} (f : A -> B) (A' : B -> Prop) : term205 A B f A'.
Proof. exact (fun s : A -> Prop => @lem3616260 A B s f A'). Qed.
Lemma lem3616270 {A B : Type'} (f : A -> B) : term206 A B f.
Proof. exact (fun A' : B -> Prop => @lem3616265 A B f A'). Qed.
Lemma lem3616275 {A B : Type'} : term207 A B.
Proof. exact (fun f : A -> B => @lem3616270 A B f). Qed.
