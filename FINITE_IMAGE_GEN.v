Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_SUBSET_spec.
Require Import FUNCTION_FACTORS_LEFT_GEN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3619180 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3619181 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3619182 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3619181 t1) (@lem3619180 t1)). Qed.
Lemma lem3619183 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3619182 t1 t2). Qed.
Lemma lem3619184 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3619185 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3619184 t1 t2) (@lem3619183 t1 t2)). Qed.
Lemma lem3619186 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3619185 t1 t2 t3). Qed.
Lemma lem3619187 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3619188 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3619187 t1 t2 t3) (@lem3619186 t1 t2 t3)). Qed.
Lemma lem3619189 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3619188 t1 t2 t3)). Qed.
Lemma lem3619190 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : term7 _91760 _91764 _91765 P.
Proof. exact (@lem3580897 _91760 _91764 _91765 P). Qed.
Lemma lem3619191 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : (term7 _91760 _91764 _91765 P) = (term8 _91760 _91764 _91765 P).
Proof. exact (eq_refl (term7 _91760 _91764 _91765 P)). Qed.
Lemma lem3619192 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : term8 _91760 _91764 _91765 P.
Proof. exact (EQ_MP (@lem3619191 _91760 _91764 _91765 P) (@lem3619190 _91760 _91764 _91765 P)). Qed.
Lemma lem3619193 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : term9 _91760 _91764 _91765 P f.
Proof. exact (@lem3619192 _91760 _91764 _91765 P f). Qed.
Lemma lem3619194 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : (term9 _91760 _91764 _91765 P f) = (term10 _91760 _91764 _91765 P f).
Proof. exact (eq_refl (term9 _91760 _91764 _91765 P f)). Qed.
Lemma lem3619195 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : term10 _91760 _91764 _91765 P f.
Proof. exact (EQ_MP (@lem3619194 _91760 _91764 _91765 P f) (@lem3619193 _91760 _91764 _91765 P f)). Qed.
Lemma lem3619196 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) (g : _91765 -> _91764) : term11 _91760 _91764 _91765 P f g.
Proof. exact (@lem3619195 _91760 _91764 _91765 P f g). Qed.
Lemma lem3619197 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) (g : _91765 -> _91764) : (term11 _91760 _91764 _91765 P f g) = ((term12 _91760 _91764 _91765 P g f) = (term13 _91760 _91764 _91765 P f g)).
Proof. exact (eq_refl (term11 _91760 _91764 _91765 P f g)). Qed.
Lemma lem3619199 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term14 A B C t s f g) : term14 A B C t s f g.
Proof. exact (h1). Qed.
Lemma lem3619200 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term15 A B C t s f g) : term15 A B C t s f g.
Proof. exact (h1). Qed.
Lemma lem3619201 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term16 A B f s t.
Proof. exact (h1). Qed.
Lemma lem3619202 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term17 A B C s f g) : term17 A B C s f g.
Proof. exact (h1). Qed.
Lemma lem3619203 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem3619205 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) (g : _91765 -> _91764) : (term12 _91760 _91764 _91765 P g f) = (term13 _91760 _91764 _91765 P f g).
Proof. exact (EQ_MP (@lem3619197 _91760 _91764 _91765 P f g) (@lem3619196 _91760 _91764 _91765 P f g)). Qed.
Lemma lem3619206 {A B C : Type'} (P : A -> Prop) (f : A -> C) (g : A -> B) : (term18 A B C P g f) = (term19 A B C P f g).
Proof. exact (@lem3619205 C B A P f g). Qed.
Lemma lem3619207 {A B C : Type'} (s : A -> Prop) (g : A -> C) (f : A -> B) : (term20 A B C s f g) = (term21 A B C s g f).
Proof. exact (@lem3619206 A B C (term22 A s) g f). Qed.
Lemma lem3619208 {A : Type'} (x : A) (s : A -> Prop) : (term23 A s x) = (@IN A x s).
Proof. exact (eq_refl (term23 A s x)). Qed.
Lemma lem3619209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619210 {A : Type'} (x : A) (s : A -> Prop) : (term24 A s x) = (term25 A x s).
Proof. exact (MK_COMB (@lem3619209) (@lem3619208 A x s)). Qed.
Lemma lem3619211 {A : Type'} (y : A) (s : A -> Prop) : (term23 A s y) = (@IN A y s).
Proof. exact (eq_refl (term23 A s y)). Qed.
Lemma lem3619212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619213 {A : Type'} (y : A) (s : A -> Prop) : (term24 A s y) = (term25 A y s).
Proof. exact (MK_COMB (@lem3619212) (@lem3619211 A y s)). Qed.
Lemma lem3619214 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3619215 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term26 A B s x f y) = (term27 A B s x f y).
Proof. exact (MK_COMB (@lem3619213 A y s) (@lem3619214 A B x f y)). Qed.
Lemma lem3619216 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term28 A B s x f y) = (term29 A B s x f y).
Proof. exact (MK_COMB (@lem3619210 A x s) (@lem3619215 A B s x f y)). Qed.
Lemma lem3619217 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619218 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (y : A) : (term30 A B s x f y) = (term31 A B s x f y).
Proof. exact (MK_COMB (@lem3619217) (@lem3619216 A B s x f y)). Qed.
Lemma lem3619219 {A C : Type'} (x : A) (g : A -> C) (y : A) : ((g x) = (g y)) = ((g x) = (g y)).
Proof. exact (eq_refl ((g x) = (g y))). Qed.
Lemma lem3619220 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g : A -> C) (y : A) : (term32 A B C s f x g y) = (term33 A B C s f x g y).
Proof. exact (MK_COMB (@lem3619218 A B s x f y) (@lem3619219 A C x g y)). Qed.
Lemma lem3619221 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g : A -> C) : (term34 A B C s f x g) = (term35 A B C s f x g).
Proof. exact (fun_ext (fun y : A => @lem3619220 A B C s f x g y)). Qed.
Lemma lem3619222 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619223 {A B C : Type'} (s : A -> Prop) (f : A -> B) (x : A) (g : A -> C) : (term36 A B C s f x g) = (term37 A B C s f x g).
Proof. exact (MK_COMB (@lem3619222 A) (@lem3619221 A B C s f x g)). Qed.
Lemma lem3619224 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) : (term38 A B C s f g) = (term39 A B C s f g).
Proof. exact (fun_ext (fun x : A => @lem3619223 A B C s f x g)). Qed.
Lemma lem3619225 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619226 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) : (term20 A B C s f g) = (term17 A B C s f g).
Proof. exact (MK_COMB (@lem3619225 A) (@lem3619224 A B C s f g)). Qed.
Lemma lem3619227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3619228 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) : (term40 A B C s f g) = (term41 A B C s f g).
Proof. exact (MK_COMB (@lem3619227) (@lem3619226 A B C s f g)). Qed.
Lemma lem3619229 {A : Type'} (x : A) (s : A -> Prop) : (term23 A s x) = (@IN A x s).
Proof. exact (eq_refl (term23 A s x)). Qed.
Lemma lem3619230 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619231 {A : Type'} (x : A) (s : A -> Prop) : (term42 A s x) = (term43 A x s).
Proof. exact (MK_COMB (@lem3619230) (@lem3619229 A x s)). Qed.
Lemma lem3619232 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : ((g x) = (term44 A B C h f x)) = ((g x) = (term44 A B C h f x)).
Proof. exact (eq_refl ((g x) = (term44 A B C h f x))). Qed.
Lemma lem3619233 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term45 A B C s g h f x) = (term46 A B C s g h f x).
Proof. exact (MK_COMB (@lem3619231 A x s) (@lem3619232 A B C g h f x)). Qed.
Lemma lem3619234 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term47 A B C s g h f) = (term48 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3619233 A B C s g h f x)). Qed.
Lemma lem3619235 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619236 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term49 A B C s g h f) = (term50 A B C s g h f).
Proof. exact (MK_COMB (@lem3619235 A) (@lem3619234 A B C s g h f)). Qed.
Lemma lem3619237 {A B C : Type'} (s : A -> Prop) (g : A -> C) (f : A -> B) : (term51 A B C s g f) = (term52 A B C s g f).
Proof. exact (fun_ext (fun h : B -> C => @lem3619236 A B C s g h f)). Qed.
Lemma lem3619238 {B C : Type'} : (@ex (B -> C)) = (@ex (B -> C)).
Proof. exact (eq_refl (@ex (B -> C))). Qed.
Lemma lem3619239 {A B C : Type'} (s : A -> Prop) (g : A -> C) (f : A -> B) : (term21 A B C s g f) = (term53 A B C s g f).
Proof. exact (MK_COMB (@lem3619238 B C) (@lem3619237 A B C s g f)). Qed.
Lemma lem3619240 {A B C : Type'} (s : A -> Prop) (g : A -> C) (f : A -> B) : ((term20 A B C s f g) = (term21 A B C s g f)) = ((term17 A B C s f g) = (term53 A B C s g f)).
Proof. exact (MK_COMB (@lem3619228 A B C s f g) (@lem3619239 A B C s g f)). Qed.
Lemma lem3619241 {A B C : Type'} (s : A -> Prop) (g : A -> C) (f : A -> B) : (term17 A B C s f g) = (term53 A B C s g f).
Proof. exact (EQ_MP (@lem3619240 A B C s g f) (@lem3619207 A B C s g f)). Qed.
Lemma lem3619242 {A B C : Type'} (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term17 A B C s f g) : term53 A B C s g f.
Proof. exact (EQ_MP (@lem3619241 A B C s g f) (@lem3619202 A B C s f g h1)). Qed.
Lemma lem3619243 {A B C : Type'} (s : A -> Prop) (g : A -> C) (f : A -> B) (h1 : term53 A B C s g f) : term53 A B C s g f.
Proof. exact (h1). Qed.
Lemma lem3619244 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (h1 : term50 A B C s g h f) : term50 A B C s g h f.
Proof. exact (h1). Qed.
Lemma lem3619245 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : (@IMAGE A C g s) = (term54 A B C h f s)) : (@IMAGE A C g s) = (term54 A B C h f s).
Proof. exact (h1). Qed.
Lemma lem3619246 {C : Type'} : (term55 C) = (term55 C).
Proof. exact (eq_refl (term55 C)). Qed.
Lemma lem3619247 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : (@IMAGE A C g s) = (term54 A B C h f s)) : (term56 A C g s) = (term57 A B C h f s).
Proof. exact (MK_COMB (@lem3619246 C) (@lem3619245 A B C g h f s h1)). Qed.
Lemma lem3619248 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term57 A B C h f s) = (term58 A B C h f s).
Proof. exact (eq_refl (term57 A B C h f s)). Qed.
Lemma lem3619249 {A C : Type'} (g : A -> C) (s : A -> Prop) : (term59 A C g s) = (term59 A C g s).
Proof. exact (eq_refl (term59 A C g s)). Qed.
Lemma lem3619250 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term56 A C g s) = (term57 A B C h f s)) = ((term56 A C g s) = (term58 A B C h f s)).
Proof. exact (MK_COMB (@lem3619249 A C g s) (@lem3619248 A B C h f s)). Qed.
Lemma lem3619251 {A C : Type'} (g : A -> C) (s : A -> Prop) : (term56 A C g s) = (term60 A C g s).
Proof. exact (eq_refl (term56 A C g s)). Qed.
Lemma lem3619252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3619253 {A C : Type'} (g : A -> C) (s : A -> Prop) : (term59 A C g s) = (term61 A C g s).
Proof. exact (MK_COMB (@lem3619252) (@lem3619251 A C g s)). Qed.
Lemma lem3619254 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term58 A B C h f s) = (term58 A B C h f s).
Proof. exact (eq_refl (term58 A B C h f s)). Qed.
Lemma lem3619255 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term56 A C g s) = (term58 A B C h f s)) = ((term60 A C g s) = (term58 A B C h f s)).
Proof. exact (MK_COMB (@lem3619253 A C g s) (@lem3619254 A B C h f s)). Qed.
Lemma lem3619256 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term56 A C g s) = (term57 A B C h f s)) = ((term60 A C g s) = (term58 A B C h f s)).
Proof. exact (TRANS (@lem3619250 A B C g h f s) (@lem3619255 A B C g h f s)). Qed.
Lemma lem3619257 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : (@IMAGE A C g s) = (term54 A B C h f s)) : (term60 A C g s) = (term58 A B C h f s).
Proof. exact (EQ_MP (@lem3619256 A B C g h f s) (@lem3619247 A B C g h f s h1)). Qed.
Lemma lem3619258 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : (@IMAGE A C g s) = (term54 A B C h f s)) : (term58 A B C h f s) = (term60 A C g s).
Proof. exact (SYM (@lem3619257 A B C g h f s h1)). Qed.
Lemma lem3619269 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term16 A B f s t) : term62 A B f s t.
Proof. exact (conj (@lem3619203 B t h1) (@lem3619201 A B f s t h2)). Qed.
Lemma lem3619270 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term63 A B C g h f s t.
Proof. exact (conj (@lem3619244 A B C s g h f h1) (@lem3619269 A B f s t h2 h3)). Qed.
Lemma lem3619288 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term64 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3619289 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (@SUBSET B s t) = (term64 B s t).
Proof. exact (@lem3619288 B s t). Qed.
Lemma lem3619290 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term16 A B f s t) = (term65 A B f s t).
Proof. exact (@lem3619289 B (@IMAGE A B f s) t). Qed.
Lemma lem3619297 {B : Type'} (t : B -> Prop) : (term66 B t) = (term66 B t).
Proof. exact (eq_refl (term66 B t)). Qed.
Lemma lem3619298 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term62 A B f s t) = (term67 A B f s t).
Proof. exact (MK_COMB (@lem3619297 B t) (@lem3619290 A B f s t)). Qed.
Lemma lem3619301 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term68 A B C s g h f) = (term68 A B C s g h f).
Proof. exact (eq_refl (term68 A B C s g h f)). Qed.
Lemma lem3619302 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term63 A B C g h f s t) = (term69 A B C g h f s t).
Proof. exact (MK_COMB (@lem3619301 A B C s g h f) (@lem3619298 A B f s t)). Qed.
Lemma lem3619305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619306 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term70 A B C g h f s t) = (term71 A B C g h f s t).
Proof. exact (MK_COMB (@lem3619305) (@lem3619302 A B C g h f s t)). Qed.
Lemma lem3619310 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term72 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3619311 {C : Type'} (s : C -> Prop) (t : C -> Prop) : (s = t) = (term72 C s t).
Proof. exact (@lem3619310 C s t). Qed.
Lemma lem3619312 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((@IMAGE A C g s) = (term54 A B C h f s)) = (term73 A B C g h f s).
Proof. exact (@lem3619311 C (@IMAGE A C g s) (term54 A B C h f s)). Qed.
Lemma lem3619321 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term74 A B C t g h f s) = (term75 A B C t g h f s).
Proof. exact (MK_COMB (@lem3619306 A B C g h f s t) (@lem3619312 A B C g h f s)). Qed.
Lemma lem3619324 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term75 A B C t g h f s) = (term74 A B C t g h f s).
Proof. exact (SYM (@lem3619321 A B C t g h f s)). Qed.
Lemma lem3619336 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3619337 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3619336 A P x). Qed.
Lemma lem3619338 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3619337 A s x). Qed.
Lemma lem3619339 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619340 {A : Type'} (s : A -> Prop) (x : A) : (term43 A x s) = (term76 A s x).
Proof. exact (MK_COMB (@lem3619339) (@lem3619338 A s x)). Qed.
Lemma lem3619343 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : ((g x) = (term44 A B C h f x)) = ((g x) = (term44 A B C h f x)).
Proof. exact (eq_refl ((g x) = (term44 A B C h f x))). Qed.
Lemma lem3619344 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term46 A B C s g h f x) = (term77 A B C s g h f x).
Proof. exact (MK_COMB (@lem3619340 A s x) (@lem3619343 A B C g h f x)). Qed.
Lemma lem3619347 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term48 A B C s g h f) = (term78 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3619344 A B C s g h f x)). Qed.
Lemma lem3619348 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619349 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term50 A B C s g h f) = (term79 A B C s g h f).
Proof. exact (MK_COMB (@lem3619348 A) (@lem3619347 A B C s g h f)). Qed.
Lemma lem3619354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619355 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term68 A B C s g h f) = (term80 A B C s g h f).
Proof. exact (MK_COMB (@lem3619354) (@lem3619349 A B C s g h f)). Qed.
Lemma lem3619365 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term81 A B y f s) = (term82 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3619366 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term81 A B y f s) = (term82 A B y f s).
Proof. exact (@lem3619365 A B y f s). Qed.
Lemma lem3619367 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B x f s) = (term82 A B x f s).
Proof. exact (@lem3619366 A B x f s). Qed.
Lemma lem3619377 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3619378 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3619377 A P x). Qed.
Lemma lem3619379 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3619378 A s x). Qed.
Lemma lem3619380 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term83 A B x f x') = (term83 A B x f x').
Proof. exact (eq_refl (term83 A B x f x')). Qed.
Lemma lem3619381 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term84 A B x f x' s) = (term85 A B x f s x').
Proof. exact (MK_COMB (@lem3619380 A B x f x') (@lem3619379 A s x')). Qed.
Lemma lem3619384 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term86 A B x f s) = (term87 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3619381 A B x f s x')). Qed.
Lemma lem3619385 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3619386 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term82 A B x f s) = (term88 A B x f s).
Proof. exact (MK_COMB (@lem3619385 A) (@lem3619384 A B x f s)). Qed.
Lemma lem3619391 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B x f s) = (term88 A B x f s).
Proof. exact (TRANS (@lem3619367 A B x f s) (@lem3619386 A B x f s)). Qed.
Lemma lem3619392 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619393 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term89 A B x f s) = (term90 A B x f s).
Proof. exact (MK_COMB (@lem3619392) (@lem3619391 A B x f s)). Qed.
Lemma lem3619395 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3619396 {B : Type'} (P : B -> Prop) (x : B) : (@IN B x P) = (P x).
Proof. exact (@lem3619395 B P x). Qed.
Lemma lem3619397 {B : Type'} (t : B -> Prop) (x : B) : (@IN B x t) = (t x).
Proof. exact (@lem3619396 B t x). Qed.
Lemma lem3619398 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term91 A B f s x t) = (term92 A B f s t x).
Proof. exact (MK_COMB (@lem3619393 A B x f s) (@lem3619397 B t x)). Qed.
Lemma lem3619401 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term93 A B f s t) = (term94 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem3619398 A B f s t x)). Qed.
Lemma lem3619402 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3619403 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term65 A B f s t) = (term95 A B f s t).
Proof. exact (MK_COMB (@lem3619402 B) (@lem3619401 A B f s t)). Qed.
Lemma lem3619408 {B : Type'} (t : B -> Prop) : (term66 B t) = (term66 B t).
Proof. exact (eq_refl (term66 B t)). Qed.
Lemma lem3619409 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term67 A B f s t) = (term96 A B f s t).
Proof. exact (MK_COMB (@lem3619408 B t) (@lem3619403 A B f s t)). Qed.
Lemma lem3619412 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term69 A B C g h f s t) = (term97 A B C g h f s t).
Proof. exact (MK_COMB (@lem3619355 A B C s g h f) (@lem3619409 A B f s t)). Qed.
Lemma lem3619415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619416 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term71 A B C g h f s t) = (term98 A B C g h f s t).
Proof. exact (MK_COMB (@lem3619415) (@lem3619412 A B C g h f s t)). Qed.
Lemma lem3619424 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term81 A B y f s) = (term82 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3619425 {A C : Type'} (y : C) (f : A -> C) (s : A -> Prop) : (term81 A C y f s) = (term82 A C y f s).
Proof. exact (@lem3619424 A C y f s). Qed.
Lemma lem3619426 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term81 A C x g s) = (term82 A C x g s).
Proof. exact (@lem3619425 A C x g s). Qed.
Lemma lem3619436 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3619437 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3619436 A P x). Qed.
Lemma lem3619438 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3619437 A s x). Qed.
Lemma lem3619439 {A C : Type'} (x : C) (g : A -> C) (x' : A) : (term83 A C x g x') = (term83 A C x g x').
Proof. exact (eq_refl (term83 A C x g x')). Qed.
Lemma lem3619440 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term84 A C x g x' s) = (term85 A C x g s x').
Proof. exact (MK_COMB (@lem3619439 A C x g x') (@lem3619438 A s x')). Qed.
Lemma lem3619443 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term86 A C x g s) = (term87 A C x g s).
Proof. exact (fun_ext (fun x' : A => @lem3619440 A C x g s x')). Qed.
Lemma lem3619444 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3619445 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term82 A C x g s) = (term88 A C x g s).
Proof. exact (MK_COMB (@lem3619444 A) (@lem3619443 A C x g s)). Qed.
Lemma lem3619450 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term81 A C x g s) = (term88 A C x g s).
Proof. exact (TRANS (@lem3619426 A C x g s) (@lem3619445 A C x g s)). Qed.
Lemma lem3619451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3619452 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term99 A C x g s) = (term100 A C x g s).
Proof. exact (MK_COMB (@lem3619451) (@lem3619450 A C x g s)). Qed.
Lemma lem3619454 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term81 A B y f s) = (term82 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3619455 {B C : Type'} (y : C) (f : B -> C) (s : B -> Prop) : (term81 B C y f s) = (term82 B C y f s).
Proof. exact (@lem3619454 B C y f s). Qed.
Lemma lem3619456 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term101 A B C x h f s) = (term102 A B C x h f s).
Proof. exact (@lem3619455 B C x h (@IMAGE A B f s)). Qed.
Lemma lem3619466 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term81 A B y f s) = (term82 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem3619467 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term81 A B y f s) = (term82 A B y f s).
Proof. exact (@lem3619466 A B y f s). Qed.
Lemma lem3619468 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B x f s) = (term82 A B x f s).
Proof. exact (@lem3619467 A B x f s). Qed.
Lemma lem3619478 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3619479 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3619478 A P x). Qed.
Lemma lem3619480 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3619479 A s x). Qed.
Lemma lem3619481 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term83 A B x f x') = (term83 A B x f x').
Proof. exact (eq_refl (term83 A B x f x')). Qed.
Lemma lem3619482 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term84 A B x f x' s) = (term85 A B x f s x').
Proof. exact (MK_COMB (@lem3619481 A B x f x') (@lem3619480 A s x')). Qed.
Lemma lem3619485 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term86 A B x f s) = (term87 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3619482 A B x f s x')). Qed.
Lemma lem3619486 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3619487 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term82 A B x f s) = (term88 A B x f s).
Proof. exact (MK_COMB (@lem3619486 A) (@lem3619485 A B x f s)). Qed.
Lemma lem3619492 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term81 A B x f s) = (term88 A B x f s).
Proof. exact (TRANS (@lem3619468 A B x f s) (@lem3619487 A B x f s)). Qed.
Lemma lem3619493 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term83 B C x h x') = (term83 B C x h x').
Proof. exact (eq_refl (term83 B C x h x')). Qed.
Lemma lem3619494 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term103 A B C x h x' f s) = (term104 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3619493 B C x h x') (@lem3619492 A B x' f s)). Qed.
Lemma lem3619497 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term105 A B C x h f s) = (term106 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3619494 A B C x h x' f s)). Qed.
Lemma lem3619498 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3619499 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term102 A B C x h f s) = (term107 A B C x h f s).
Proof. exact (MK_COMB (@lem3619498 B) (@lem3619497 A B C x h f s)). Qed.
Lemma lem3619504 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term101 A B C x h f s) = (term107 A B C x h f s).
Proof. exact (TRANS (@lem3619456 A B C x h f s) (@lem3619499 A B C x h f s)). Qed.
Lemma lem3619505 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term81 A C x g s) = (term101 A B C x h f s)) = ((term88 A C x g s) = (term107 A B C x h f s)).
Proof. exact (MK_COMB (@lem3619452 A C x g s) (@lem3619504 A B C x h f s)). Qed.
Lemma lem3619508 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term108 A B C g h f s) = (term109 A B C g h f s).
Proof. exact (fun_ext (fun x : C => @lem3619505 A B C g x h f s)). Qed.
Lemma lem3619509 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3619510 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term73 A B C g h f s) = (term110 A B C g h f s).
Proof. exact (MK_COMB (@lem3619509 C) (@lem3619508 A B C g h f s)). Qed.
Lemma lem3619515 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term75 A B C t g h f s) = (term111 A B C t g h f s).
Proof. exact (MK_COMB (@lem3619416 A B C g h f s t) (@lem3619510 A B C g h f s)). Qed.
Lemma lem3619518 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term111 A B C t g h f s) = (term75 A B C t g h f s).
Proof. exact (SYM (@lem3619515 A B C t g h f s)). Qed.
Lemma lem3619520 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3619521 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term111 A B C t g h f s) = (term113 A B C t g h f s).
Proof. exact (@lem3619520 (term111 A B C t g h f s)). Qed.
Lemma lem3619522 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term113 A B C t g h f s) = (term111 A B C t g h f s).
Proof. exact (SYM (@lem3619521 A B C t g h f s)). Qed.
Lemma lem3619523 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term114 A B C t g h f s) : term114 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3619526 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term113 A B C t g h f s) : term113 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3619527 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term115 A B C t g h f s.
Proof. exact (fun h0 : term113 A B C t g h f s => @lem3619526 A B C t g h f s h0). Qed.
Lemma lem3619528 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term115 A B C t g h f s) : term115 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3619529 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term113 A B C t g h f s) : term113 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3619530 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term113 A B C t g h f s) (h2 : term115 A B C t g h f s) : term113 A B C t g h f s.
Proof. exact (@lem3619528 A B C t g h f s h2 (@lem3619529 A B C t g h f s h1)). Qed.
Lemma lem3619531 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term113 A B C t g h f s) : term116 A B C t g h f s.
Proof. exact (fun h0 : term115 A B C t g h f s => @lem3619530 A B C t g h f s h1 h0). Qed.
Lemma lem3619532 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term115 A B C t g h f s) : term115 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3619533 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term113 A B C t g h f s) (h2 : term115 A B C t g h f s) : term113 A B C t g h f s.
Proof. exact (@lem3619531 A B C t g h f s h1 (@lem3619532 A B C t g h f s h2)). Qed.
Lemma lem3619534 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term115 A B C t g h f s) : term115 A B C t g h f s.
Proof. exact (fun h0 : term113 A B C t g h f s => @lem3619533 A B C t g h f s h0 h1). Qed.
Lemma lem3619535 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term117 A B C t g h f s.
Proof. exact (fun h0 : term115 A B C t g h f s => @lem3619534 A B C t g h f s h0). Qed.
Lemma lem3619538 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term115 A B C t g h f s.
Proof. exact (@lem3619535 A B C t g h f s (@lem3619527 A B C t g h f s)). Qed.
Lemma lem3619539 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term115 A B C t g h f s.
Proof. exact (@lem3619538 A B C t g h f s). Qed.
Lemma lem3619561 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3619562 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term113 A B C t g h f s) = (term118 A B C t g h f s).
Proof. exact (@lem3619561 (term114 A B C t g h f s)). Qed.
Lemma lem3619564 (t : Prop) : (term119 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3619565 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term118 A B C t g h f s) = (term111 A B C t g h f s).
Proof. exact (@lem3619564 (term111 A B C t g h f s)). Qed.
Lemma lem3619568 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term113 A B C t g h f s) = (term111 A B C t g h f s).
Proof. exact (TRANS (@lem3619562 A B C t g h f s) (@lem3619565 A B C t g h f s)). Qed.
Lemma lem3619741 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term120 A B C g h f s) = (term121 A B C g h f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3619568 A B C t g h f s)). Qed.
Lemma lem3619742 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3619743 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term122 A B C g h f s) = (term123 A B C g h f s).
Proof. exact (MK_COMB (@lem3619742 B) (@lem3619741 A B C g h f s)). Qed.
Lemma lem3619748 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term124 A B C h f s) = (term125 A B C h f s).
Proof. exact (fun_ext (fun g : A -> C => @lem3619743 A B C g h f s)). Qed.
Lemma lem3619749 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem3619750 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term126 A B C h f s) = (term127 A B C h f s).
Proof. exact (MK_COMB (@lem3619749 A C) (@lem3619748 A B C h f s)). Qed.
Lemma lem3619755 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term128 A B C f s) = (term129 A B C f s).
Proof. exact (fun_ext (fun h : B -> C => @lem3619750 A B C h f s)). Qed.
Lemma lem3619756 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3619757 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term130 A B C f s) = (term131 A B C f s).
Proof. exact (MK_COMB (@lem3619756 B C) (@lem3619755 A B C f s)). Qed.
Lemma lem3619762 {A B C : Type'} (s : A -> Prop) : (term132 A B C s) = (term133 A B C s).
Proof. exact (fun_ext (fun f : A -> B => @lem3619757 A B C f s)). Qed.
Lemma lem3619763 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3619764 {A B C : Type'} (s : A -> Prop) : (term134 A B C s) = (term135 A B C s).
Proof. exact (MK_COMB (@lem3619763 A B) (@lem3619762 A B C s)). Qed.
Lemma lem3619769 {A B C : Type'} : (term136 A B C) = (term137 A B C).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3619764 A B C s)). Qed.
Lemma lem3619770 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3619779 {A B C : Type'} : (term138 A B C) = (term139 A B C).
Proof. exact (MK_COMB (@lem3619770 A) (@lem3619769 A B C)). Qed.
Lemma lem3619784 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term85 A B x f s x') = (term85 A B x f s x').
Proof. exact (eq_refl (term85 A B x f s x')). Qed.
Lemma lem3619785 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term87 A B x f s) = (term87 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3619784 A B x f s x')). Qed.
Lemma lem3619786 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3619787 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term88 A B x f s) = (term88 A B x f s).
Proof. exact (MK_COMB (@lem3619786 A) (@lem3619785 A B x f s)). Qed.
Lemma lem3619790 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term83 B C x h x') = (term83 B C x h x').
Proof. exact (eq_refl (term83 B C x h x')). Qed.
Lemma lem3619791 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term104 A B C x h x' f s) = (term104 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3619790 B C x h x') (@lem3619787 A B x' f s)). Qed.
Lemma lem3619792 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term106 A B C x h f s) = (term106 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3619791 A B C x h x' f s)). Qed.
Lemma lem3619793 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3619794 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term107 A B C x h f s) = (term107 A B C x h f s).
Proof. exact (MK_COMB (@lem3619793 B) (@lem3619792 A B C x h f s)). Qed.
Lemma lem3619799 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term85 A C x g s x') = (term85 A C x g s x').
Proof. exact (eq_refl (term85 A C x g s x')). Qed.
Lemma lem3619800 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term87 A C x g s) = (term87 A C x g s).
Proof. exact (fun_ext (fun x' : A => @lem3619799 A C x g s x')). Qed.
Lemma lem3619801 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3619802 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term88 A C x g s) = (term88 A C x g s).
Proof. exact (MK_COMB (@lem3619801 A) (@lem3619800 A C x g s)). Qed.
Lemma lem3619803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3619804 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term100 A C x g s) = (term100 A C x g s).
Proof. exact (MK_COMB (@lem3619803) (@lem3619802 A C x g s)). Qed.
Lemma lem3619805 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term88 A C x g s) = (term107 A B C x h f s)) = ((term88 A C x g s) = (term107 A B C x h f s)).
Proof. exact (MK_COMB (@lem3619804 A C x g s) (@lem3619794 A B C x h f s)). Qed.
Lemma lem3619806 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term109 A B C g h f s) = (term109 A B C g h f s).
Proof. exact (fun_ext (fun x : C => @lem3619805 A B C g x h f s)). Qed.
Lemma lem3619807 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem3619808 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term110 A B C g h f s) = (term110 A B C g h f s).
Proof. exact (MK_COMB (@lem3619807 C) (@lem3619806 A B C g h f s)). Qed.
Lemma lem3619809 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3619814 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term85 A B x f s x') = (term85 A B x f s x').
Proof. exact (eq_refl (term85 A B x f s x')). Qed.
Lemma lem3619815 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term87 A B x f s) = (term87 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3619814 A B x f s x')). Qed.
Lemma lem3619816 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3619817 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term88 A B x f s) = (term88 A B x f s).
Proof. exact (MK_COMB (@lem3619816 A) (@lem3619815 A B x f s)). Qed.
Lemma lem3619818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619819 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term90 A B x f s) = (term90 A B x f s).
Proof. exact (MK_COMB (@lem3619818) (@lem3619817 A B x f s)). Qed.
Lemma lem3619820 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term92 A B f s t x) = (term92 A B f s t x).
Proof. exact (MK_COMB (@lem3619819 A B x f s) (@lem3619809 B t x)). Qed.
Lemma lem3619821 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term94 A B f s t) = (term94 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem3619820 A B f s t x)). Qed.
Lemma lem3619822 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3619823 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term95 A B f s t) = (term95 A B f s t).
Proof. exact (MK_COMB (@lem3619822 B) (@lem3619821 A B f s t)). Qed.
Lemma lem3619826 {B : Type'} (t : B -> Prop) : (term66 B t) = (term66 B t).
Proof. exact (eq_refl (term66 B t)). Qed.
Lemma lem3619827 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term96 A B f s t) = (term96 A B f s t).
Proof. exact (MK_COMB (@lem3619826 B t) (@lem3619823 A B f s t)). Qed.
Lemma lem3619832 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term77 A B C s g h f x) = (term77 A B C s g h f x).
Proof. exact (eq_refl (term77 A B C s g h f x)). Qed.
Lemma lem3619833 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term78 A B C s g h f) = (term78 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3619832 A B C s g h f x)). Qed.
Lemma lem3619834 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619835 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term79 A B C s g h f) = (term79 A B C s g h f).
Proof. exact (MK_COMB (@lem3619834 A) (@lem3619833 A B C s g h f)). Qed.
Lemma lem3619836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619837 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term80 A B C s g h f) = (term80 A B C s g h f).
Proof. exact (MK_COMB (@lem3619836) (@lem3619835 A B C s g h f)). Qed.
Lemma lem3619838 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term97 A B C g h f s t) = (term97 A B C g h f s t).
Proof. exact (MK_COMB (@lem3619837 A B C s g h f) (@lem3619827 A B f s t)). Qed.
Lemma lem3619839 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3619840 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term98 A B C g h f s t) = (term98 A B C g h f s t).
Proof. exact (MK_COMB (@lem3619839) (@lem3619838 A B C g h f s t)). Qed.
Lemma lem3619841 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term111 A B C t g h f s) = (term111 A B C t g h f s).
Proof. exact (MK_COMB (@lem3619840 A B C g h f s t) (@lem3619808 A B C g h f s)). Qed.
Lemma lem3619842 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term121 A B C g h f s) = (term121 A B C g h f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3619841 A B C t g h f s)). Qed.
Lemma lem3619843 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3619844 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term123 A B C g h f s) = (term123 A B C g h f s).
Proof. exact (MK_COMB (@lem3619843 B) (@lem3619842 A B C g h f s)). Qed.
Lemma lem3619845 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term125 A B C h f s) = (term125 A B C h f s).
Proof. exact (fun_ext (fun g : A -> C => @lem3619844 A B C g h f s)). Qed.
Lemma lem3619846 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem3619847 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term127 A B C h f s) = (term127 A B C h f s).
Proof. exact (MK_COMB (@lem3619846 A C) (@lem3619845 A B C h f s)). Qed.
Lemma lem3619848 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term129 A B C f s) = (term129 A B C f s).
Proof. exact (fun_ext (fun h : B -> C => @lem3619847 A B C h f s)). Qed.
Lemma lem3619849 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3619850 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term131 A B C f s) = (term131 A B C f s).
Proof. exact (MK_COMB (@lem3619849 B C) (@lem3619848 A B C f s)). Qed.
Lemma lem3619851 {A B C : Type'} (s : A -> Prop) : (term133 A B C s) = (term133 A B C s).
Proof. exact (fun_ext (fun f : A -> B => @lem3619850 A B C f s)). Qed.
Lemma lem3619852 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3619853 {A B C : Type'} (s : A -> Prop) : (term135 A B C s) = (term135 A B C s).
Proof. exact (MK_COMB (@lem3619852 A B) (@lem3619851 A B C s)). Qed.
Lemma lem3619854 {A B C : Type'} : (term137 A B C) = (term137 A B C).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3619853 A B C s)). Qed.
Lemma lem3619855 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3619856 {A B C : Type'} : (term139 A B C) = (term139 A B C).
Proof. exact (MK_COMB (@lem3619855 A) (@lem3619854 A B C)). Qed.
Lemma lem3619949 {A B C : Type'} : (term138 A B C) = (term139 A B C).
Proof. exact (TRANS (@lem3619779 A B C) (@lem3619856 A B C)). Qed.
Lemma lem3619950 {A B C : Type'} : (term139 A B C) = (term138 A B C).
Proof. exact (SYM (@lem3619949 A B C)). Qed.
Lemma lem3619951 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term97 A B C g h f s t.
Proof. exact (h1). Qed.
Lemma lem3619953 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3619954 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term88 A C x g s) = (term107 A B C x h f s)) = (term140 A B C g x h f s).
Proof. exact (@lem3619953 ((term88 A C x g s) = (term107 A B C x h f s))). Qed.
Lemma lem3619955 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term140 A B C g x h f s) = ((term88 A C x g s) = (term107 A B C x h f s)).
Proof. exact (SYM (@lem3619954 A B C g x h f s)). Qed.
Lemma lem3619956 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term141 A B C g x h f s) : term141 A B C g x h f s.
Proof. exact (h1). Qed.
Lemma lem3619963 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term77 A B C s g h f x) = (term142 A B C s g h f x).
Proof. exact (@lem17265 (s x) ((g x) = (term44 A B C h f x))). Qed.
Lemma lem3619964 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term78 A B C s g h f) = (term143 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3619963 A B C s g h f x)). Qed.
Lemma lem3619965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619966 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term79 A B C s g h f) = (term144 A B C s g h f).
Proof. exact (MK_COMB (@lem3619965 A) (@lem3619964 A B C s g h f)). Qed.
Lemma lem3619974 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term145 A B x f s x') = (term146 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3619975 {A : Type'} (P : A -> Prop) : (term147 A P) = (term148 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3619976 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term150 A B x f s).
Proof. exact (@lem3619975 A (term87 A B x f s)). Qed.
Lemma lem3619977 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term151 A B x f s x') = (term85 A B x f s x').
Proof. exact (eq_refl (term151 A B x f s x')). Qed.
Lemma lem3619978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3619979 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term152 A B x f s x') = (term145 A B x f s x').
Proof. exact (MK_COMB (@lem3619978) (@lem3619977 A B x f s x')). Qed.
Lemma lem3619980 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term152 A B x f s x') = (term146 A B x f s x').
Proof. exact (TRANS (@lem3619979 A B x f s x') (@lem3619974 A B x f s x')). Qed.
Lemma lem3619981 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term153 A B x f s) = (term154 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3619980 A B x f s x')). Qed.
Lemma lem3619982 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3619983 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term150 A B x f s) = (term155 A B x f s).
Proof. exact (MK_COMB (@lem3619982 A) (@lem3619981 A B x f s)). Qed.
Lemma lem3619984 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term155 A B x f s).
Proof. exact (TRANS (@lem3619976 A B x f s) (@lem3619983 A B x f s)). Qed.
Lemma lem3619985 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3619986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3619987 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term156 A B x f s) = (term157 A B x f s).
Proof. exact (MK_COMB (@lem3619986) (@lem3619984 A B x f s)). Qed.
Lemma lem3619988 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term158 A B f s t x) = (term159 A B f s t x).
Proof. exact (MK_COMB (@lem3619987 A B x f s) (@lem3619985 B t x)). Qed.
Lemma lem3619989 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term92 A B f s t x) = (term158 A B f s t x).
Proof. exact (@lem17265 (term88 A B x f s) (t x)). Qed.
Lemma lem3619990 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term92 A B f s t x) = (term159 A B f s t x).
Proof. exact (TRANS (@lem3619989 A B f s t x) (@lem3619988 A B f s t x)). Qed.
Lemma lem3619991 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term94 A B f s t) = (term160 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem3619990 A B f s t x)). Qed.
Lemma lem3619992 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3619993 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term95 A B f s t) = (term161 A B f s t).
Proof. exact (MK_COMB (@lem3619992 B) (@lem3619991 A B f s t)). Qed.
Lemma lem3619995 {B : Type'} (t : B -> Prop) : (term66 B t) = (term66 B t).
Proof. exact (eq_refl (term66 B t)). Qed.
Lemma lem3619996 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term96 A B f s t) = (term162 A B f s t).
Proof. exact (MK_COMB (@lem3619995 B t) (@lem3619993 A B f s t)). Qed.
Lemma lem3619997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3619998 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term80 A B C s g h f) = (term163 A B C s g h f).
Proof. exact (MK_COMB (@lem3619997) (@lem3619966 A B C s g h f)). Qed.
Lemma lem3620131 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term97 A B C g h f s t) = (term164 A B C g h f s t).
Proof. exact (MK_COMB (@lem3619998 A B C s g h f) (@lem3619996 A B f s t)). Qed.
Lemma lem3620132 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term164 A B C g h f s t.
Proof. exact (EQ_MP (@lem3620131 A B C g h f s t) (@lem3619951 A B C g h f s t h1)). Qed.
Lemma lem3620141 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term145 A C x g s x') = (term146 A C x g s x').
Proof. exact (@lem17045 (x = (g x')) (s x')). Qed.
Lemma lem3620144 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term85 A C x g s x') = (term85 A C x g s x').
Proof. exact (eq_refl (term85 A C x g s x')). Qed.
Lemma lem3620145 {A : Type'} (P : A -> Prop) : (term147 A P) = (term148 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3620146 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term149 A C x g s) = (term150 A C x g s).
Proof. exact (@lem3620145 A (term87 A C x g s)). Qed.
Lemma lem3620147 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term151 A C x g s x') = (term85 A C x g s x').
Proof. exact (eq_refl (term151 A C x g s x')). Qed.
Lemma lem3620148 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3620149 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term152 A C x g s x') = (term145 A C x g s x').
Proof. exact (MK_COMB (@lem3620148) (@lem3620147 A C x g s x')). Qed.
Lemma lem3620150 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term152 A C x g s x') = (term146 A C x g s x').
Proof. exact (TRANS (@lem3620149 A C x g s x') (@lem3620141 A C x g s x')). Qed.
Lemma lem3620151 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term153 A C x g s) = (term154 A C x g s).
Proof. exact (fun_ext (fun x' : A => @lem3620150 A C x g s x')). Qed.
Lemma lem3620152 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620153 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term150 A C x g s) = (term155 A C x g s).
Proof. exact (MK_COMB (@lem3620152 A) (@lem3620151 A C x g s)). Qed.
Lemma lem3620154 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term149 A C x g s) = (term155 A C x g s).
Proof. exact (TRANS (@lem3620146 A C x g s) (@lem3620153 A C x g s)). Qed.
Lemma lem3620155 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term87 A C x g s) = (term87 A C x g s).
Proof. exact (fun_ext (fun x' : A => @lem3620144 A C x g s x')). Qed.
Lemma lem3620156 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620157 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term88 A C x g s) = (term88 A C x g s).
Proof. exact (MK_COMB (@lem3620156 A) (@lem3620155 A C x g s)). Qed.
Lemma lem3620168 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term145 A B x f s x') = (term146 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem3620171 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term85 A B x f s x') = (term85 A B x f s x').
Proof. exact (eq_refl (term85 A B x f s x')). Qed.
Lemma lem3620172 {A : Type'} (P : A -> Prop) : (term147 A P) = (term148 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3620173 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term150 A B x f s).
Proof. exact (@lem3620172 A (term87 A B x f s)). Qed.
Lemma lem3620174 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term151 A B x f s x') = (term85 A B x f s x').
Proof. exact (eq_refl (term151 A B x f s x')). Qed.
Lemma lem3620175 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3620176 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term152 A B x f s x') = (term145 A B x f s x').
Proof. exact (MK_COMB (@lem3620175) (@lem3620174 A B x f s x')). Qed.
Lemma lem3620177 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term152 A B x f s x') = (term146 A B x f s x').
Proof. exact (TRANS (@lem3620176 A B x f s x') (@lem3620168 A B x f s x')). Qed.
Lemma lem3620178 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term153 A B x f s) = (term154 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3620177 A B x f s x')). Qed.
Lemma lem3620179 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620180 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term150 A B x f s) = (term155 A B x f s).
Proof. exact (MK_COMB (@lem3620179 A) (@lem3620178 A B x f s)). Qed.
Lemma lem3620181 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term149 A B x f s) = (term155 A B x f s).
Proof. exact (TRANS (@lem3620173 A B x f s) (@lem3620180 A B x f s)). Qed.
Lemma lem3620182 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term87 A B x f s) = (term87 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3620171 A B x f s x')). Qed.
Lemma lem3620183 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620184 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term88 A B x f s) = (term88 A B x f s).
Proof. exact (MK_COMB (@lem3620183 A) (@lem3620182 A B x f s)). Qed.
Lemma lem3620186 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term165 B C x h x') = (term165 B C x h x').
Proof. exact (eq_refl (term165 B C x h x')). Qed.
Lemma lem3620187 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term166 A B C x h x' f s) = (term167 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620186 B C x h x') (@lem3620181 A B x' f s)). Qed.
Lemma lem3620188 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term168 A B C x h x' f s) = (term166 A B C x h x' f s).
Proof. exact (@lem17045 (x = (h x')) (term88 A B x' f s)). Qed.
Lemma lem3620189 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term168 A B C x h x' f s) = (term167 A B C x h x' f s).
Proof. exact (TRANS (@lem3620188 A B C x h x' f s) (@lem3620187 A B C x h x' f s)). Qed.
Lemma lem3620191 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term83 B C x h x') = (term83 B C x h x').
Proof. exact (eq_refl (term83 B C x h x')). Qed.
Lemma lem3620192 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term104 A B C x h x' f s) = (term104 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620191 B C x h x') (@lem3620184 A B x' f s)). Qed.
Lemma lem3620193 {B : Type'} (P : B -> Prop) : (term147 B P) = (term148 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem3620194 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term169 A B C x h f s) = (term170 A B C x h f s).
Proof. exact (@lem3620193 B (term106 A B C x h f s)). Qed.
Lemma lem3620195 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term171 A B C x h f s x') = (term104 A B C x h x' f s).
Proof. exact (eq_refl (term171 A B C x h f s x')). Qed.
Lemma lem3620196 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3620197 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term172 A B C x h f s x') = (term168 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620196) (@lem3620195 A B C x h x' f s)). Qed.
Lemma lem3620198 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term172 A B C x h f s x') = (term167 A B C x h x' f s).
Proof. exact (TRANS (@lem3620197 A B C x h x' f s) (@lem3620189 A B C x h x' f s)). Qed.
Lemma lem3620199 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term173 A B C x h f s) = (term174 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620198 A B C x h x' f s)). Qed.
Lemma lem3620200 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3620201 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term170 A B C x h f s) = (term175 A B C x h f s).
Proof. exact (MK_COMB (@lem3620200 B) (@lem3620199 A B C x h f s)). Qed.
Lemma lem3620202 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term169 A B C x h f s) = (term175 A B C x h f s).
Proof. exact (TRANS (@lem3620194 A B C x h f s) (@lem3620201 A B C x h f s)). Qed.
Lemma lem3620203 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term106 A B C x h f s) = (term106 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620192 A B C x h x' f s)). Qed.
Lemma lem3620204 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620205 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term107 A B C x h f s) = (term107 A B C x h f s).
Proof. exact (MK_COMB (@lem3620204 B) (@lem3620203 A B C x h f s)). Qed.
Lemma lem3620206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3620207 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term176 A C x g s) = (term177 A C x g s).
Proof. exact (MK_COMB (@lem3620206) (@lem3620154 A C x g s)). Qed.
Lemma lem3620208 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term178 A B C g x h f s) = (term179 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620207 A C x g s) (@lem3620205 A B C x h f s)). Qed.
Lemma lem3620209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3620210 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term180 A C x g s) = (term180 A C x g s).
Proof. exact (MK_COMB (@lem3620209) (@lem3620157 A C x g s)). Qed.
Lemma lem3620211 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term181 A B C g x h f s) = (term182 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620210 A C x g s) (@lem3620202 A B C x h f s)). Qed.
Lemma lem3620212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3620213 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term183 A B C g x h f s) = (term184 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620212) (@lem3620211 A B C g x h f s)). Qed.
Lemma lem3620214 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term185 A B C g x h f s) = (term186 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620213 A B C g x h f s) (@lem3620208 A B C g x h f s)). Qed.
Lemma lem3620215 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term141 A B C g x h f s) = (term185 A B C g x h f s).
Proof. exact (@lem17646 (term88 A C x g s) (term107 A B C x h f s)). Qed.
Lemma lem3620216 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term141 A B C g x h f s) = (term186 A B C g x h f s).
Proof. exact (TRANS (@lem3620215 A B C g x h f s) (@lem3620214 A B C g x h f s)). Qed.
Lemma lem3620475 {A : Type'} (P : A -> Prop) (Q : Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3620476 {A : Type'} (P : A -> Prop) (Q : Prop) : (term187 A P Q) = (term188 A P Q).
Proof. exact (@lem3620475 A P Q). Qed.
Lemma lem3620477 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term189 A B C g x h f s) = (term190 A B C g x h f s).
Proof. exact (@lem3620476 A (term87 A C x g s) (term175 A B C x h f s)). Qed.
Lemma lem3620478 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term151 A C x g s x') = (term85 A C x g s x').
Proof. exact (eq_refl (term151 A C x g s x')). Qed.
Lemma lem3620479 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term191 A C x g s) = (term87 A C x g s).
Proof. exact (fun_ext (fun x' : A => @lem3620478 A C x g s x')). Qed.
Lemma lem3620480 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620481 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term192 A C x g s) = (term88 A C x g s).
Proof. exact (MK_COMB (@lem3620480 A) (@lem3620479 A C x g s)). Qed.
Lemma lem3620482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3620483 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term193 A C x g s) = (term180 A C x g s).
Proof. exact (MK_COMB (@lem3620482) (@lem3620481 A C x g s)). Qed.
Lemma lem3620484 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term175 A B C x h f s) = (term175 A B C x h f s).
Proof. exact (eq_refl (term175 A B C x h f s)). Qed.
Lemma lem3620485 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term189 A B C g x h f s) = (term182 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620483 A C x g s) (@lem3620484 A B C x h f s)). Qed.
Lemma lem3620486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620487 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term194 A B C g x h f s) = (term195 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620486) (@lem3620485 A B C g x h f s)). Qed.
Lemma lem3620488 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term151 A C x g s x') = (term85 A C x g s x').
Proof. exact (eq_refl (term151 A C x g s x')). Qed.
Lemma lem3620489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3620490 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term196 A C x g s x') = (term197 A C x g s x').
Proof. exact (MK_COMB (@lem3620489) (@lem3620488 A C x g s x')). Qed.
Lemma lem3620491 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term175 A B C x h f s) = (term175 A B C x h f s).
Proof. exact (eq_refl (term175 A B C x h f s)). Qed.
Lemma lem3620492 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term198 A B C g x x' h f s) = (term199 A B C g x x' h f s).
Proof. exact (MK_COMB (@lem3620490 A C x' g s x) (@lem3620491 A B C x' h f s)). Qed.
Lemma lem3620493 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term200 A B C g x h f s) = (term201 A B C g x h f s).
Proof. exact (fun_ext (fun x' : A => @lem3620492 A B C g x' x h f s)). Qed.
Lemma lem3620494 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620495 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term190 A B C g x h f s) = (term202 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620494 A) (@lem3620493 A B C g x h f s)). Qed.
Lemma lem3620496 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term189 A B C g x h f s) = (term190 A B C g x h f s)) = ((term182 A B C g x h f s) = (term202 A B C g x h f s)).
Proof. exact (MK_COMB (@lem3620487 A B C g x h f s) (@lem3620495 A B C g x h f s)). Qed.
Lemma lem3620497 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term182 A B C g x h f s) = (term202 A B C g x h f s).
Proof. exact (EQ_MP (@lem3620496 A B C g x h f s) (@lem3620477 A B C g x h f s)). Qed.
Lemma lem3620498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3620499 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term184 A B C g x h f s) = (term203 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620498) (@lem3620497 A B C g x h f s)). Qed.
Lemma lem3620501 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3620502 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (@lem3620501 A P Q). Qed.
Lemma lem3620503 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term206 A B C x h x' f s) = (term207 A B C x h x' f s).
Proof. exact (@lem3620502 A (x = (h x')) (term87 A B x' f s)). Qed.
Lemma lem3620504 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term151 A B x f s x') = (term85 A B x f s x').
Proof. exact (eq_refl (term151 A B x f s x')). Qed.
Lemma lem3620505 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term191 A B x f s) = (term87 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3620504 A B x f s x')). Qed.
Lemma lem3620506 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620507 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term192 A B x f s) = (term88 A B x f s).
Proof. exact (MK_COMB (@lem3620506 A) (@lem3620505 A B x f s)). Qed.
Lemma lem3620508 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term83 B C x h x') = (term83 B C x h x').
Proof. exact (eq_refl (term83 B C x h x')). Qed.
Lemma lem3620509 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term206 A B C x h x' f s) = (term104 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620508 B C x h x') (@lem3620507 A B x' f s)). Qed.
Lemma lem3620510 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620511 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term208 A B C x h x' f s) = (term209 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620510) (@lem3620509 A B C x h x' f s)). Qed.
Lemma lem3620512 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term151 A B x f s x') = (term85 A B x f s x').
Proof. exact (eq_refl (term151 A B x f s x')). Qed.
Lemma lem3620513 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term83 B C x h x') = (term83 B C x h x').
Proof. exact (eq_refl (term83 B C x h x')). Qed.
Lemma lem3620514 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term210 A B C x h x' f s x'') = (term211 A B C x h x' f s x'').
Proof. exact (MK_COMB (@lem3620513 B C x h x') (@lem3620512 A B x' f s x'')). Qed.
Lemma lem3620515 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term212 A B C x h x' f s) = (term213 A B C x h x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3620514 A B C x h x' f s x'')). Qed.
Lemma lem3620516 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620517 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term207 A B C x h x' f s) = (term214 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620516 A) (@lem3620515 A B C x h x' f s)). Qed.
Lemma lem3620518 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : ((term206 A B C x h x' f s) = (term207 A B C x h x' f s)) = ((term104 A B C x h x' f s) = (term214 A B C x h x' f s)).
Proof. exact (MK_COMB (@lem3620511 A B C x h x' f s) (@lem3620517 A B C x h x' f s)). Qed.
Lemma lem3620519 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term104 A B C x h x' f s) = (term214 A B C x h x' f s).
Proof. exact (EQ_MP (@lem3620518 A B C x h x' f s) (@lem3620503 A B C x h x' f s)). Qed.
Lemma lem3620520 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term106 A B C x h f s) = (term215 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620519 A B C x h x' f s)). Qed.
Lemma lem3620521 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620522 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term107 A B C x h f s) = (term216 A B C x h f s).
Proof. exact (MK_COMB (@lem3620521 B) (@lem3620520 A B C x h f s)). Qed.
Lemma lem3620523 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term177 A C x g s) = (term177 A C x g s).
Proof. exact (eq_refl (term177 A C x g s)). Qed.
Lemma lem3620524 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term179 A B C g x h f s) = (term217 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620523 A C x g s) (@lem3620522 A B C x h f s)). Qed.
Lemma lem3620526 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3620527 {B : Type'} (P : Prop) (Q : B -> Prop) : (term204 B P Q) = (term205 B P Q).
Proof. exact (@lem3620526 B P Q). Qed.
Lemma lem3620528 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term218 A B C g x h f s) = (term219 A B C g x h f s).
Proof. exact (@lem3620527 B (term155 A C x g s) (term215 A B C x h f s)). Qed.
Lemma lem3620529 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term220 A B C x h f s x') = (term214 A B C x h x' f s).
Proof. exact (eq_refl (term220 A B C x h f s x')). Qed.
Lemma lem3620530 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term221 A B C x h f s) = (term215 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620529 A B C x h x' f s)). Qed.
Lemma lem3620531 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620532 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term222 A B C x h f s) = (term216 A B C x h f s).
Proof. exact (MK_COMB (@lem3620531 B) (@lem3620530 A B C x h f s)). Qed.
Lemma lem3620533 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term177 A C x g s) = (term177 A C x g s).
Proof. exact (eq_refl (term177 A C x g s)). Qed.
Lemma lem3620534 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term218 A B C g x h f s) = (term217 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620533 A C x g s) (@lem3620532 A B C x h f s)). Qed.
Lemma lem3620535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620536 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term223 A B C g x h f s) = (term224 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620535) (@lem3620534 A B C g x h f s)). Qed.
Lemma lem3620537 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term220 A B C x h f s x') = (term214 A B C x h x' f s).
Proof. exact (eq_refl (term220 A B C x h f s x')). Qed.
Lemma lem3620538 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term177 A C x g s) = (term177 A C x g s).
Proof. exact (eq_refl (term177 A C x g s)). Qed.
Lemma lem3620539 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term225 A B C g x h f s x') = (term226 A B C g x h x' f s).
Proof. exact (MK_COMB (@lem3620538 A C x g s) (@lem3620537 A B C x h x' f s)). Qed.
Lemma lem3620540 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term227 A B C g x h f s) = (term228 A B C g x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620539 A B C g x h x' f s)). Qed.
Lemma lem3620541 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620542 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term219 A B C g x h f s) = (term229 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620541 B) (@lem3620540 A B C g x h f s)). Qed.
Lemma lem3620543 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term218 A B C g x h f s) = (term219 A B C g x h f s)) = ((term217 A B C g x h f s) = (term229 A B C g x h f s)).
Proof. exact (MK_COMB (@lem3620536 A B C g x h f s) (@lem3620542 A B C g x h f s)). Qed.
Lemma lem3620544 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term217 A B C g x h f s) = (term229 A B C g x h f s).
Proof. exact (EQ_MP (@lem3620543 A B C g x h f s) (@lem3620528 A B C g x h f s)). Qed.
Lemma lem3620546 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3620547 {A : Type'} (P : Prop) (Q : A -> Prop) : (term204 A P Q) = (term205 A P Q).
Proof. exact (@lem3620546 A P Q). Qed.
Lemma lem3620548 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term230 A B C g x h x' f s) = (term231 A B C g x h x' f s).
Proof. exact (@lem3620547 A (term155 A C x g s) (term213 A B C x h x' f s)). Qed.
Lemma lem3620549 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term232 A B C x h x' f s x'') = (term211 A B C x h x' f s x'').
Proof. exact (eq_refl (term232 A B C x h x' f s x'')). Qed.
Lemma lem3620550 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term233 A B C x h x' f s) = (term213 A B C x h x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3620549 A B C x h x' f s x'')). Qed.
Lemma lem3620551 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620552 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term234 A B C x h x' f s) = (term214 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620551 A) (@lem3620550 A B C x h x' f s)). Qed.
Lemma lem3620553 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term177 A C x g s) = (term177 A C x g s).
Proof. exact (eq_refl (term177 A C x g s)). Qed.
Lemma lem3620554 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term230 A B C g x h x' f s) = (term226 A B C g x h x' f s).
Proof. exact (MK_COMB (@lem3620553 A C x g s) (@lem3620552 A B C x h x' f s)). Qed.
Lemma lem3620555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620556 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term235 A B C g x h x' f s) = (term236 A B C g x h x' f s).
Proof. exact (MK_COMB (@lem3620555) (@lem3620554 A B C g x h x' f s)). Qed.
Lemma lem3620557 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term232 A B C x h x' f s x'') = (term211 A B C x h x' f s x'').
Proof. exact (eq_refl (term232 A B C x h x' f s x'')). Qed.
Lemma lem3620558 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term177 A C x g s) = (term177 A C x g s).
Proof. exact (eq_refl (term177 A C x g s)). Qed.
Lemma lem3620559 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term237 A B C g x h x' f s x'') = (term238 A B C g x h x' f s x'').
Proof. exact (MK_COMB (@lem3620558 A C x g s) (@lem3620557 A B C x h x' f s x'')). Qed.
Lemma lem3620560 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term239 A B C g x h x' f s) = (term240 A B C g x h x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3620559 A B C g x h x' f s x'')). Qed.
Lemma lem3620561 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620562 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term231 A B C g x h x' f s) = (term241 A B C g x h x' f s).
Proof. exact (MK_COMB (@lem3620561 A) (@lem3620560 A B C g x h x' f s)). Qed.
Lemma lem3620563 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : ((term230 A B C g x h x' f s) = (term231 A B C g x h x' f s)) = ((term226 A B C g x h x' f s) = (term241 A B C g x h x' f s)).
Proof. exact (MK_COMB (@lem3620556 A B C g x h x' f s) (@lem3620562 A B C g x h x' f s)). Qed.
Lemma lem3620564 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term226 A B C g x h x' f s) = (term241 A B C g x h x' f s).
Proof. exact (EQ_MP (@lem3620563 A B C g x h x' f s) (@lem3620548 A B C g x h x' f s)). Qed.
Lemma lem3620565 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term228 A B C g x h f s) = (term242 A B C g x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620564 A B C g x h x' f s)). Qed.
Lemma lem3620566 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620567 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term229 A B C g x h f s) = (term243 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620566 B) (@lem3620565 A B C g x h f s)). Qed.
Lemma lem3620568 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term217 A B C g x h f s) = (term243 A B C g x h f s).
Proof. exact (TRANS (@lem3620544 A B C g x h f s) (@lem3620567 A B C g x h f s)). Qed.
Lemma lem3620569 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term179 A B C g x h f s) = (term243 A B C g x h f s).
Proof. exact (TRANS (@lem3620524 A B C g x h f s) (@lem3620568 A B C g x h f s)). Qed.
Lemma lem3620570 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term186 A B C g x h f s) = (term244 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620499 A B C g x h f s) (@lem3620569 A B C g x h f s)). Qed.
Lemma lem3620574 {A : Type'} (P : A -> Prop) (Q : Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3620575 {A : Type'} (P : A -> Prop) (Q : Prop) : (term245 A P Q) = (term246 A P Q).
Proof. exact (@lem3620574 A P Q). Qed.
Lemma lem3620576 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term247 A B C g x h f s) = (term248 A B C g x h f s).
Proof. exact (@lem3620575 A (term201 A B C g x h f s) (term243 A B C g x h f s)). Qed.
Lemma lem3620577 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term249 A B C g x' h f s x) = (term199 A B C g x x' h f s).
Proof. exact (eq_refl (term249 A B C g x' h f s x)). Qed.
Lemma lem3620578 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term250 A B C g x h f s) = (term201 A B C g x h f s).
Proof. exact (fun_ext (fun x' : A => @lem3620577 A B C g x' x h f s)). Qed.
Lemma lem3620579 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620580 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term251 A B C g x h f s) = (term202 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620579 A) (@lem3620578 A B C g x h f s)). Qed.
Lemma lem3620581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3620582 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term252 A B C g x h f s) = (term203 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620581) (@lem3620580 A B C g x h f s)). Qed.
Lemma lem3620583 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term243 A B C g x h f s) = (term243 A B C g x h f s).
Proof. exact (eq_refl (term243 A B C g x h f s)). Qed.
Lemma lem3620584 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term247 A B C g x h f s) = (term244 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620582 A B C g x h f s) (@lem3620583 A B C g x h f s)). Qed.
Lemma lem3620585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620586 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term253 A B C g x h f s) = (term254 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620585) (@lem3620584 A B C g x h f s)). Qed.
Lemma lem3620587 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term249 A B C g x' h f s x) = (term199 A B C g x x' h f s).
Proof. exact (eq_refl (term249 A B C g x' h f s x)). Qed.
Lemma lem3620588 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3620589 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term255 A B C g x' h f s x) = (term256 A B C g x x' h f s).
Proof. exact (MK_COMB (@lem3620588) (@lem3620587 A B C g x x' h f s)). Qed.
Lemma lem3620590 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term243 A B C g x h f s) = (term243 A B C g x h f s).
Proof. exact (eq_refl (term243 A B C g x h f s)). Qed.
Lemma lem3620591 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term257 A B C x g x' h f s) = (term258 A B C x g x' h f s).
Proof. exact (MK_COMB (@lem3620589 A B C g x x' h f s) (@lem3620590 A B C g x' h f s)). Qed.
Lemma lem3620592 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term259 A B C g x h f s) = (term260 A B C g x h f s).
Proof. exact (fun_ext (fun x' : A => @lem3620591 A B C x' g x h f s)). Qed.
Lemma lem3620593 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620594 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term248 A B C g x h f s) = (term261 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620593 A) (@lem3620592 A B C g x h f s)). Qed.
Lemma lem3620595 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term247 A B C g x h f s) = (term248 A B C g x h f s)) = ((term244 A B C g x h f s) = (term261 A B C g x h f s)).
Proof. exact (MK_COMB (@lem3620586 A B C g x h f s) (@lem3620594 A B C g x h f s)). Qed.
Lemma lem3620596 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term244 A B C g x h f s) = (term261 A B C g x h f s).
Proof. exact (EQ_MP (@lem3620595 A B C g x h f s) (@lem3620576 A B C g x h f s)). Qed.
Lemma lem3620598 {A : Type'} (P : Prop) (Q : A -> Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3620599 {B : Type'} (P : Prop) (Q : B -> Prop) : (term262 B P Q) = (term263 B P Q).
Proof. exact (@lem3620598 B P Q). Qed.
Lemma lem3620600 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term264 A B C x g x' h f s) = (term265 A B C x g x' h f s).
Proof. exact (@lem3620599 B (term199 A B C g x x' h f s) (term242 A B C g x' h f s)). Qed.
Lemma lem3620601 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term266 A B C g x h f s x') = (term241 A B C g x h x' f s).
Proof. exact (eq_refl (term266 A B C g x h f s x')). Qed.
Lemma lem3620602 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term267 A B C g x h f s) = (term242 A B C g x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620601 A B C g x h x' f s)). Qed.
Lemma lem3620603 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620604 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term268 A B C g x h f s) = (term243 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620603 B) (@lem3620602 A B C g x h f s)). Qed.
Lemma lem3620605 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term256 A B C g x x' h f s) = (term256 A B C g x x' h f s).
Proof. exact (eq_refl (term256 A B C g x x' h f s)). Qed.
Lemma lem3620606 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term264 A B C x g x' h f s) = (term258 A B C x g x' h f s).
Proof. exact (MK_COMB (@lem3620605 A B C g x x' h f s) (@lem3620604 A B C g x' h f s)). Qed.
Lemma lem3620607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620608 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term269 A B C x g x' h f s) = (term270 A B C x g x' h f s).
Proof. exact (MK_COMB (@lem3620607) (@lem3620606 A B C x g x' h f s)). Qed.
Lemma lem3620609 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term266 A B C g x h f s x') = (term241 A B C g x h x' f s).
Proof. exact (eq_refl (term266 A B C g x h f s x')). Qed.
Lemma lem3620610 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term256 A B C g x x' h f s) = (term256 A B C g x x' h f s).
Proof. exact (eq_refl (term256 A B C g x x' h f s)). Qed.
Lemma lem3620611 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : (term271 A B C x g x' h f s x'') = (term272 A B C x g x' h x'' f s).
Proof. exact (MK_COMB (@lem3620610 A B C g x x' h f s) (@lem3620609 A B C g x' h x'' f s)). Qed.
Lemma lem3620612 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term273 A B C x g x' h f s) = (term274 A B C x g x' h f s).
Proof. exact (fun_ext (fun x'' : B => @lem3620611 A B C x g x' h x'' f s)). Qed.
Lemma lem3620613 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620614 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term265 A B C x g x' h f s) = (term275 A B C x g x' h f s).
Proof. exact (MK_COMB (@lem3620613 B) (@lem3620612 A B C x g x' h f s)). Qed.
Lemma lem3620615 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : ((term264 A B C x g x' h f s) = (term265 A B C x g x' h f s)) = ((term258 A B C x g x' h f s) = (term275 A B C x g x' h f s)).
Proof. exact (MK_COMB (@lem3620608 A B C x g x' h f s) (@lem3620614 A B C x g x' h f s)). Qed.
Lemma lem3620616 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term258 A B C x g x' h f s) = (term275 A B C x g x' h f s).
Proof. exact (EQ_MP (@lem3620615 A B C x g x' h f s) (@lem3620600 A B C x g x' h f s)). Qed.
Lemma lem3620618 {A : Type'} (P : Prop) (Q : A -> Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3620619 {A : Type'} (P : Prop) (Q : A -> Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (@lem3620618 A P Q). Qed.
Lemma lem3620620 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : (term276 A B C x g x' h x'' f s) = (term277 A B C x g x' h x'' f s).
Proof. exact (@lem3620619 A (term199 A B C g x x' h f s) (term240 A B C g x' h x'' f s)). Qed.
Lemma lem3620621 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term278 A B C g x h x' f s x'') = (term238 A B C g x h x' f s x'').
Proof. exact (eq_refl (term278 A B C g x h x' f s x'')). Qed.
Lemma lem3620622 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term279 A B C g x h x' f s) = (term240 A B C g x h x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3620621 A B C g x h x' f s x'')). Qed.
Lemma lem3620623 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620624 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term280 A B C g x h x' f s) = (term241 A B C g x h x' f s).
Proof. exact (MK_COMB (@lem3620623 A) (@lem3620622 A B C g x h x' f s)). Qed.
Lemma lem3620625 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term256 A B C g x x' h f s) = (term256 A B C g x x' h f s).
Proof. exact (eq_refl (term256 A B C g x x' h f s)). Qed.
Lemma lem3620626 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : (term276 A B C x g x' h x'' f s) = (term272 A B C x g x' h x'' f s).
Proof. exact (MK_COMB (@lem3620625 A B C g x x' h f s) (@lem3620624 A B C g x' h x'' f s)). Qed.
Lemma lem3620627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620628 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : (term281 A B C x g x' h x'' f s) = (term282 A B C x g x' h x'' f s).
Proof. exact (MK_COMB (@lem3620627) (@lem3620626 A B C x g x' h x'' f s)). Qed.
Lemma lem3620629 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term278 A B C g x h x' f s x'') = (term238 A B C g x h x' f s x'').
Proof. exact (eq_refl (term278 A B C g x h x' f s x'')). Qed.
Lemma lem3620630 {A B C : Type'} (g : A -> C) (x : A) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term256 A B C g x x' h f s) = (term256 A B C g x x' h f s).
Proof. exact (eq_refl (term256 A B C g x x' h f s)). Qed.
Lemma lem3620631 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term283 A B C x g x' h x'' f s x''') = (term284 A B C x g x' h x'' f s x''').
Proof. exact (MK_COMB (@lem3620630 A B C g x x' h f s) (@lem3620629 A B C g x' h x'' f s x''')). Qed.
Lemma lem3620632 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : (term285 A B C x g x' h x'' f s) = (term286 A B C x g x' h x'' f s).
Proof. exact (fun_ext (fun x''' : A => @lem3620631 A B C x g x' h x'' f s x''')). Qed.
Lemma lem3620633 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620634 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : (term277 A B C x g x' h x'' f s) = (term287 A B C x g x' h x'' f s).
Proof. exact (MK_COMB (@lem3620633 A) (@lem3620632 A B C x g x' h x'' f s)). Qed.
Lemma lem3620635 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : ((term276 A B C x g x' h x'' f s) = (term277 A B C x g x' h x'' f s)) = ((term272 A B C x g x' h x'' f s) = (term287 A B C x g x' h x'' f s)).
Proof. exact (MK_COMB (@lem3620628 A B C x g x' h x'' f s) (@lem3620634 A B C x g x' h x'' f s)). Qed.
Lemma lem3620636 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) : (term272 A B C x g x' h x'' f s) = (term287 A B C x g x' h x'' f s).
Proof. exact (EQ_MP (@lem3620635 A B C x g x' h x'' f s) (@lem3620620 A B C x g x' h x'' f s)). Qed.
Lemma lem3620637 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term274 A B C x g x' h f s) = (term288 A B C x g x' h f s).
Proof. exact (fun_ext (fun x'' : B => @lem3620636 A B C x g x' h x'' f s)). Qed.
Lemma lem3620638 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3620639 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term275 A B C x g x' h f s) = (term289 A B C x g x' h f s).
Proof. exact (MK_COMB (@lem3620638 B) (@lem3620637 A B C x g x' h f s)). Qed.
Lemma lem3620640 {A B C : Type'} (x : A) (g : A -> C) (x' : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term258 A B C x g x' h f s) = (term289 A B C x g x' h f s).
Proof. exact (TRANS (@lem3620616 A B C x g x' h f s) (@lem3620639 A B C x g x' h f s)). Qed.
Lemma lem3620641 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term260 A B C g x h f s) = (term290 A B C g x h f s).
Proof. exact (fun_ext (fun x' : A => @lem3620640 A B C x' g x h f s)). Qed.
Lemma lem3620642 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3620643 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term261 A B C g x h f s) = (term291 A B C g x h f s).
Proof. exact (MK_COMB (@lem3620642 A) (@lem3620641 A B C g x h f s)). Qed.
Lemma lem3620644 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term244 A B C g x h f s) = (term291 A B C g x h f s).
Proof. exact (TRANS (@lem3620596 A B C g x h f s) (@lem3620643 A B C g x h f s)). Qed.
Lemma lem3620646 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term186 A B C g x h f s) = (term291 A B C g x h f s).
Proof. exact (TRANS (@lem3620570 A B C g x h f s) (@lem3620644 A B C g x h f s)). Qed.
Lemma lem3620647 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term141 A B C g x h f s) = (term291 A B C g x h f s).
Proof. exact (TRANS (@lem3620216 A B C g x h f s) (@lem3620646 A B C g x h f s)). Qed.
Lemma lem3620648 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term141 A B C g x h f s) : term291 A B C g x h f s.
Proof. exact (EQ_MP (@lem3620647 A B C g x h f s) (@lem3619956 A B C g x h f s h1)). Qed.
Lemma lem3620649 {A B C : Type'} (x' : A) (g : A -> C) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term289 A B C x' g x h f s) : term289 A B C x' g x h f s.
Proof. exact (h1). Qed.
Lemma lem3620650 {A B C : Type'} (x' : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (h1 : term287 A B C x' g x h x'' f s) : term287 A B C x' g x h x'' f s.
Proof. exact (h1). Qed.
Lemma lem3620651 {A B C : Type'} (x' : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term284 A B C x' g x h x'' f s x''') : term284 A B C x' g x h x'' f s x'''.
Proof. exact (h1). Qed.
Lemma lem3620656 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3620657 {B : Type'} (f : B -> Prop) (x : B) : (f x) = (@I (B -> Prop) f x).
Proof. exact (@lem3620656 B Prop f x). Qed.
Lemma lem3620659 {B : Type'} (t : B -> Prop) (x : B) : (t x) = (@I (B -> Prop) t x).
Proof. exact (@lem3620657 B t x). Qed.
Lemma lem3620676 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term146 A B x f s x') = (term146 A B x f s x').
Proof. exact (eq_refl (term146 A B x f s x')). Qed.
Lemma lem3620677 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term154 A B x f s) = (term154 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3620676 A B x f s x')). Qed.
Lemma lem3620678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620679 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term155 A B x f s) = (term155 A B x f s).
Proof. exact (MK_COMB (@lem3620678 A) (@lem3620677 A B x f s)). Qed.
Lemma lem3620680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3620681 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term157 A B x f s) = (term157 A B x f s).
Proof. exact (MK_COMB (@lem3620680) (@lem3620679 A B x f s)). Qed.
Lemma lem3620682 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (x : B) : (term159 A B f s t x) = (term292 A B f s t x).
Proof. exact (MK_COMB (@lem3620681 A B x f s) (@lem3620659 B t x)). Qed.
Lemma lem3620683 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term160 A B f s t) = (term293 A B f s t).
Proof. exact (fun_ext (fun x : B => @lem3620682 A B f s t x)). Qed.
Lemma lem3620684 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3620685 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term161 A B f s t) = (term294 A B f s t).
Proof. exact (MK_COMB (@lem3620684 B) (@lem3620683 A B f s t)). Qed.
Lemma lem3620690 {B : Type'} (t : B -> Prop) : (term66 B t) = (term66 B t).
Proof. exact (eq_refl (term66 B t)). Qed.
Lemma lem3620691 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term162 A B f s t) = (term295 A B f s t).
Proof. exact (MK_COMB (@lem3620690 B t) (@lem3620685 A B f s t)). Qed.
Lemma lem3620710 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term142 A B C s g h f x) = (term142 A B C s g h f x).
Proof. exact (eq_refl (term142 A B C s g h f x)). Qed.
Lemma lem3620711 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term143 A B C s g h f) = (term143 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3620710 A B C s g h f x)). Qed.
Lemma lem3620712 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620713 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term144 A B C s g h f) = (term144 A B C s g h f).
Proof. exact (MK_COMB (@lem3620712 A) (@lem3620711 A B C s g h f)). Qed.
Lemma lem3620714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3620715 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term163 A B C s g h f) = (term163 A B C s g h f).
Proof. exact (MK_COMB (@lem3620714) (@lem3620713 A B C s g h f)). Qed.
Lemma lem3620716 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term164 A B C g h f s t) = (term296 A B C g h f s t).
Proof. exact (MK_COMB (@lem3620715 A B C s g h f) (@lem3620691 A B f s t)). Qed.
Lemma lem3620717 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term296 A B C g h f s t.
Proof. exact (EQ_MP (@lem3620716 A B C g h f s t) (@lem3620132 A B C g h f s t h1)). Qed.
Lemma lem3620740 {A B C : Type'} (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term211 A B C x h x'' f s x''') = (term211 A B C x h x'' f s x''').
Proof. exact (eq_refl (term211 A B C x h x'' f s x''')). Qed.
Lemma lem3620757 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term146 A C x g s x') = (term146 A C x g s x').
Proof. exact (eq_refl (term146 A C x g s x')). Qed.
Lemma lem3620758 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term154 A C x g s) = (term154 A C x g s).
Proof. exact (fun_ext (fun x' : A => @lem3620757 A C x g s x')). Qed.
Lemma lem3620759 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620760 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term155 A C x g s) = (term155 A C x g s).
Proof. exact (MK_COMB (@lem3620759 A) (@lem3620758 A C x g s)). Qed.
Lemma lem3620761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3620762 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term177 A C x g s) = (term177 A C x g s).
Proof. exact (MK_COMB (@lem3620761) (@lem3620760 A C x g s)). Qed.
Lemma lem3620763 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term238 A B C g x h x'' f s x''') = (term238 A B C g x h x'' f s x''').
Proof. exact (MK_COMB (@lem3620762 A C x g s) (@lem3620740 A B C x h x'' f s x''')). Qed.
Lemma lem3620780 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term146 A B x f s x') = (term146 A B x f s x').
Proof. exact (eq_refl (term146 A B x f s x')). Qed.
Lemma lem3620781 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term154 A B x f s) = (term154 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3620780 A B x f s x')). Qed.
Lemma lem3620782 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620783 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term155 A B x f s) = (term155 A B x f s).
Proof. exact (MK_COMB (@lem3620782 A) (@lem3620781 A B x f s)). Qed.
Lemma lem3620794 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term165 B C x h x') = (term165 B C x h x').
Proof. exact (eq_refl (term165 B C x h x')). Qed.
Lemma lem3620795 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term167 A B C x h x' f s) = (term167 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620794 B C x h x') (@lem3620783 A B x' f s)). Qed.
Lemma lem3620796 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term174 A B C x h f s) = (term174 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620795 A B C x h x' f s)). Qed.
Lemma lem3620797 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3620798 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term175 A B C x h f s) = (term175 A B C x h f s).
Proof. exact (MK_COMB (@lem3620797 B) (@lem3620796 A B C x h f s)). Qed.
Lemma lem3620813 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term197 A C x g s x') = (term197 A C x g s x').
Proof. exact (eq_refl (term197 A C x g s x')). Qed.
Lemma lem3620814 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term199 A B C g x' x h f s) = (term199 A B C g x' x h f s).
Proof. exact (MK_COMB (@lem3620813 A C x g s x') (@lem3620798 A B C x h f s)). Qed.
Lemma lem3620815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3620816 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term256 A B C g x' x h f s) = (term256 A B C g x' x h f s).
Proof. exact (MK_COMB (@lem3620815) (@lem3620814 A B C g x' x h f s)). Qed.
Lemma lem3620817 {A B C : Type'} (x' : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) : (term284 A B C x' g x h x'' f s x''') = (term284 A B C x' g x h x'' f s x''').
Proof. exact (MK_COMB (@lem3620816 A B C g x' x h f s) (@lem3620763 A B C g x h x'' f s x''')). Qed.
Lemma lem3620818 {A B C : Type'} (x' : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term284 A B C x' g x h x'' f s x''') : term284 A B C x' g x h x'' f s x'''.
Proof. exact (EQ_MP (@lem3620817 A B C x' g x h x'' f s x''') (@lem3620651 A B C x' g x h x'' f s x''' h1)). Qed.
Lemma lem3620820 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term144 A B C s g h f.
Proof. exact (proj1 (@lem3620717 A B C g h f s t h1)). Qed.
Lemma lem3620823 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term199 A B C g x' x h f s.
Proof. exact (h1). Qed.
Lemma lem3620824 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term238 A B C g x h x'' f s x'''.
Proof. exact (h1). Qed.
Lemma lem3620825 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term175 A B C x h f s.
Proof. exact (proj2 (@lem3620823 A B C g x' x h f s h1)). Qed.
Lemma lem3620826 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term85 A C x g s x'.
Proof. exact (proj1 (@lem3620823 A B C g x' x h f s h1)). Qed.
Lemma lem3620829 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term211 A B C x h x'' f s x'''.
Proof. exact (proj2 (@lem3620824 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3620830 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term155 A C x g s.
Proof. exact (proj1 (@lem3620824 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3620831 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term85 A B x'' f s x'''.
Proof. exact (proj2 (@lem3620829 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3620842 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term142 A B C s g h f x) = (term142 A B C s g h f x).
Proof. exact (eq_refl (term142 A B C s g h f x)). Qed.
Lemma lem3620843 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term143 A B C s g h f) = (term143 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3620842 A B C s g h f x)). Qed.
Lemma lem3620844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620846 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term144 A B C s g h f) = (term144 A B C s g h f).
Proof. exact (MK_COMB (@lem3620844 A) (@lem3620843 A B C s g h f)). Qed.
Lemma lem3620847 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term144 A B C s g h f.
Proof. exact (EQ_MP (@lem3620846 A B C s g h f) (@lem3620820 A B C g h f s t h1)). Qed.
Lemma lem3620901 {A : Type'} (P : Prop) (Q : A -> Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3620902 {A : Type'} (P : Prop) (Q : A -> Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (@lem3620901 A P Q). Qed.
Lemma lem3620903 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term299 A B C x h x' f s) = (term300 A B C x h x' f s).
Proof. exact (@lem3620902 A (term301 B C x h x') (term154 A B x' f s)). Qed.
Lemma lem3620904 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term302 A B x f s x') = (term146 A B x f s x').
Proof. exact (eq_refl (term302 A B x f s x')). Qed.
Lemma lem3620905 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term303 A B x f s) = (term154 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem3620904 A B x f s x')). Qed.
Lemma lem3620906 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620907 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term304 A B x f s) = (term155 A B x f s).
Proof. exact (MK_COMB (@lem3620906 A) (@lem3620905 A B x f s)). Qed.
Lemma lem3620908 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term165 B C x h x') = (term165 B C x h x').
Proof. exact (eq_refl (term165 B C x h x')). Qed.
Lemma lem3620909 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term299 A B C x h x' f s) = (term167 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620908 B C x h x') (@lem3620907 A B x' f s)). Qed.
Lemma lem3620910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3620911 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term305 A B C x h x' f s) = (term306 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620910) (@lem3620909 A B C x h x' f s)). Qed.
Lemma lem3620912 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term302 A B x f s x') = (term146 A B x f s x').
Proof. exact (eq_refl (term302 A B x f s x')). Qed.
Lemma lem3620913 {B C : Type'} (x : C) (h : B -> C) (x' : B) : (term165 B C x h x') = (term165 B C x h x').
Proof. exact (eq_refl (term165 B C x h x')). Qed.
Lemma lem3620914 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term307 A B C x h x' f s x'') = (term308 A B C x h x' f s x'').
Proof. exact (MK_COMB (@lem3620913 B C x h x') (@lem3620912 A B x' f s x'')). Qed.
Lemma lem3620915 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term309 A B C x h x' f s) = (term310 A B C x h x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3620914 A B C x h x' f s x'')). Qed.
Lemma lem3620916 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620917 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term300 A B C x h x' f s) = (term311 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620916 A) (@lem3620915 A B C x h x' f s)). Qed.
Lemma lem3620918 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : ((term299 A B C x h x' f s) = (term300 A B C x h x' f s)) = ((term167 A B C x h x' f s) = (term311 A B C x h x' f s)).
Proof. exact (MK_COMB (@lem3620911 A B C x h x' f s) (@lem3620917 A B C x h x' f s)). Qed.
Lemma lem3620919 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term167 A B C x h x' f s) = (term311 A B C x h x' f s).
Proof. exact (EQ_MP (@lem3620918 A B C x h x' f s) (@lem3620903 A B C x h x' f s)). Qed.
Lemma lem3620920 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term174 A B C x h f s) = (term312 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620919 A B C x h x' f s)). Qed.
Lemma lem3620921 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3620922 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term175 A B C x h f s) = (term313 A B C x h f s).
Proof. exact (MK_COMB (@lem3620921 B) (@lem3620920 A B C x h f s)). Qed.
Lemma lem3620935 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) (x'' : A) : (term308 A B C x h x' f s x'') = (term308 A B C x h x' f s x'').
Proof. exact (eq_refl (term308 A B C x h x' f s x'')). Qed.
Lemma lem3620936 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term310 A B C x h x' f s) = (term310 A B C x h x' f s).
Proof. exact (fun_ext (fun x'' : A => @lem3620935 A B C x h x' f s x'')). Qed.
Lemma lem3620937 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620938 {A B C : Type'} (x : C) (h : B -> C) (x' : B) (f : A -> B) (s : A -> Prop) : (term311 A B C x h x' f s) = (term311 A B C x h x' f s).
Proof. exact (MK_COMB (@lem3620937 A) (@lem3620936 A B C x h x' f s)). Qed.
Lemma lem3620939 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term312 A B C x h f s) = (term312 A B C x h f s).
Proof. exact (fun_ext (fun x' : B => @lem3620938 A B C x h x' f s)). Qed.
Lemma lem3620940 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3620941 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term313 A B C x h f s) = (term313 A B C x h f s).
Proof. exact (MK_COMB (@lem3620940 B) (@lem3620939 A B C x h f s)). Qed.
Lemma lem3620942 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term175 A B C x h f s) = (term313 A B C x h f s).
Proof. exact (TRANS (@lem3620922 A B C x h f s) (@lem3620941 A B C x h f s)). Qed.
Lemma lem3620943 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term313 A B C x h f s.
Proof. exact (EQ_MP (@lem3620942 A B C x h f s) (@lem3620825 A B C g x' x h f s h1)). Qed.
Lemma lem3620959 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term142 A B C s g h f x) = (term142 A B C s g h f x).
Proof. exact (eq_refl (term142 A B C s g h f x)). Qed.
Lemma lem3620960 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term143 A B C s g h f) = (term143 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3620959 A B C s g h f x)). Qed.
Lemma lem3620961 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3620963 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term144 A B C s g h f) = (term144 A B C s g h f).
Proof. exact (MK_COMB (@lem3620961 A) (@lem3620960 A B C s g h f)). Qed.
Lemma lem3620964 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term144 A B C s g h f.
Proof. exact (EQ_MP (@lem3620963 A B C s g h f) (@lem3620820 A B C g h f s t h1)). Qed.
Lemma lem3621024 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (x' : A) : (term146 A C x g s x') = (term146 A C x g s x').
Proof. exact (eq_refl (term146 A C x g s x')). Qed.
Lemma lem3621025 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term154 A C x g s) = (term154 A C x g s).
Proof. exact (fun_ext (fun x' : A => @lem3621024 A C x g s x')). Qed.
Lemma lem3621026 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3621028 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) : (term155 A C x g s) = (term155 A C x g s).
Proof. exact (MK_COMB (@lem3621026 A) (@lem3621025 A C x g s)). Qed.
Lemma lem3621029 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term155 A C x g s.
Proof. exact (EQ_MP (@lem3621028 A C x g s) (@lem3620830 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621042 {A B C : Type'} (_39326 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term314 A B C s g h f _39326.
Proof. exact (@lem3620847 A B C g h f s t h1 _39326). Qed.
Lemma lem3621043 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39326 : A) : (term314 A B C s g h f _39326) = (term142 A B C s g h f _39326).
Proof. exact (eq_refl (term314 A B C s g h f _39326)). Qed.
Lemma lem3621051 {A B C : Type'} (_39329 : B) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term315 A B C x h f s _39329.
Proof. exact (@lem3620943 A B C g x' x h f s h1 _39329). Qed.
Lemma lem3621052 {A B C : Type'} (x : C) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) : (term315 A B C x h f s _39329) = (term311 A B C x h _39329 f s).
Proof. exact (eq_refl (term315 A B C x h f s _39329)). Qed.
Lemma lem3621053 {A B C : Type'} (_39329 : B) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term311 A B C x h _39329 f s.
Proof. exact (EQ_MP (@lem3621052 A B C x h _39329 f s) (@lem3621051 A B C _39329 g x' x h f s h1)). Qed.
Lemma lem3621054 {A B C : Type'} (_39329 : B) (_39330 : A) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term316 A B C x h _39329 f s _39330.
Proof. exact (@lem3621053 A B C _39329 g x' x h f s h1 _39330). Qed.
Lemma lem3621055 {A B C : Type'} (x : C) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term316 A B C x h _39329 f s _39330) = (term308 A B C x h _39329 f s _39330).
Proof. exact (eq_refl (term316 A B C x h _39329 f s _39330)). Qed.
Lemma lem3621057 {A B C : Type'} (_39331 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term314 A B C s g h f _39331.
Proof. exact (@lem3620964 A B C g h f s t h1 _39331). Qed.
Lemma lem3621058 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39331 : A) : (term314 A B C s g h f _39331) = (term142 A B C s g h f _39331).
Proof. exact (eq_refl (term314 A B C s g h f _39331)). Qed.
Lemma lem3621066 {A B C : Type'} (_39334 : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term302 A C x g s _39334.
Proof. exact (@lem3621029 A B C g x h x'' f s x''' h1 _39334). Qed.
Lemma lem3621067 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term302 A C x g s _39334) = (term146 A C x g s _39334).
Proof. exact (eq_refl (term302 A C x g s _39334)). Qed.
Lemma lem3621098 {A B C : Type'} (_39329 : B) (_39330 : A) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term308 A B C x h _39329 f s _39330.
Proof. exact (EQ_MP (@lem3621055 A B C x h _39329 f s _39330) (@lem3621054 A B C _39329 _39330 g x' x h f s h1)). Qed.
Lemma lem3621100 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : x = (g x').
Proof. exact (proj1 (@lem3620826 A B C g x' x h f s h1)). Qed.
Lemma lem3621130 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : x = (h x'').
Proof. exact (proj1 (@lem3620829 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621132 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : x'' = (f x''').
Proof. exact (proj1 (@lem3620831 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621162 {A B C : Type'} (_39326 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term142 A B C s g h f _39326.
Proof. exact (EQ_MP (@lem3621043 A B C s g h f _39326) (@lem3621042 A B C _39326 g h f s t h1)). Qed.
Lemma lem3621191 {A B C : Type'} (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term317 A B C h _39329 f s _39330) = (term317 A B C h _39329 f s _39330).
Proof. exact (eq_refl (term317 A B C h _39329 f s _39330)). Qed.
Lemma lem3621192 {A B C : Type'} (_39329 : B) (_39330 : A) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : (term318 A B C h _39329 f s _39330 x) = (term319 A B C h _39329 f s _39330 g x').
Proof. exact (MK_COMB (@lem3621191 A B C h _39329 f s _39330) (@lem3621100 A B C g x' x h f s h1)). Qed.
Lemma lem3621193 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term319 A B C h _39329 f s _39330 g x') = (term320 A B C g x' h _39329 f s _39330).
Proof. exact (eq_refl (term319 A B C h _39329 f s _39330 g x')). Qed.
Lemma lem3621194 {A B C : Type'} (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) (x : C) : (term321 A B C h _39329 f s _39330 x) = (term321 A B C h _39329 f s _39330 x).
Proof. exact (eq_refl (term321 A B C h _39329 f s _39330 x)). Qed.
Lemma lem3621195 {A B C : Type'} (x : C) (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : ((term318 A B C h _39329 f s _39330 x) = (term319 A B C h _39329 f s _39330 g x')) = ((term318 A B C h _39329 f s _39330 x) = (term320 A B C g x' h _39329 f s _39330)).
Proof. exact (MK_COMB (@lem3621194 A B C h _39329 f s _39330 x) (@lem3621193 A B C g x' h _39329 f s _39330)). Qed.
Lemma lem3621196 {A B C : Type'} (x : C) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term318 A B C h _39329 f s _39330 x) = (term308 A B C x h _39329 f s _39330).
Proof. exact (eq_refl (term318 A B C h _39329 f s _39330 x)). Qed.
Lemma lem3621197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3621198 {A B C : Type'} (x : C) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term321 A B C h _39329 f s _39330 x) = (term322 A B C x h _39329 f s _39330).
Proof. exact (MK_COMB (@lem3621197) (@lem3621196 A B C x h _39329 f s _39330)). Qed.
Lemma lem3621199 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term320 A B C g x' h _39329 f s _39330) = (term320 A B C g x' h _39329 f s _39330).
Proof. exact (eq_refl (term320 A B C g x' h _39329 f s _39330)). Qed.
Lemma lem3621200 {A B C : Type'} (x : C) (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : ((term318 A B C h _39329 f s _39330 x) = (term320 A B C g x' h _39329 f s _39330)) = ((term308 A B C x h _39329 f s _39330) = (term320 A B C g x' h _39329 f s _39330)).
Proof. exact (MK_COMB (@lem3621198 A B C x h _39329 f s _39330) (@lem3621199 A B C g x' h _39329 f s _39330)). Qed.
Lemma lem3621201 {A B C : Type'} (x : C) (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : ((term318 A B C h _39329 f s _39330 x) = (term319 A B C h _39329 f s _39330 g x')) = ((term308 A B C x h _39329 f s _39330) = (term320 A B C g x' h _39329 f s _39330)).
Proof. exact (TRANS (@lem3621195 A B C x g x' h _39329 f s _39330) (@lem3621200 A B C x g x' h _39329 f s _39330)). Qed.
Lemma lem3621202 {A B C : Type'} (_39329 : B) (_39330 : A) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : (term308 A B C x h _39329 f s _39330) = (term320 A B C g x' h _39329 f s _39330).
Proof. exact (EQ_MP (@lem3621201 A B C x g x' h _39329 f s _39330) (@lem3621192 A B C _39329 _39330 g x' x h f s h1)). Qed.
Lemma lem3621203 {A B C : Type'} (_39329 : B) (_39330 : A) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term320 A B C g x' h _39329 f s _39330.
Proof. exact (EQ_MP (@lem3621202 A B C _39329 _39330 g x' x h f s h1) (@lem3621098 A B C _39329 _39330 g x' x h f s h1)). Qed.
Lemma lem3621287 {A B C : Type'} (_39334 : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term146 A C x g s _39334.
Proof. exact (EQ_MP (@lem3621067 A C x g s _39334) (@lem3621066 A B C _39334 g x h x'' f s x''' h1)). Qed.
Lemma lem3621288 {B C : Type'} (x : C) (h : B -> C) : (term323 B C x h) = (term323 B C x h).
Proof. exact (eq_refl (term323 B C x h)). Qed.
Lemma lem3621289 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : (term324 B C x h x'') = (term325 A B C x h f x''').
Proof. exact (MK_COMB (@lem3621288 B C x h) (@lem3621132 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621290 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (x''' : A) : (term325 A B C x h f x''') = (x = (term44 A B C h f x''')).
Proof. exact (eq_refl (term325 A B C x h f x''')). Qed.
Lemma lem3621291 {B C : Type'} (x : C) (h : B -> C) (x'' : B) : (term326 B C x h x'') = (term326 B C x h x'').
Proof. exact (eq_refl (term326 B C x h x'')). Qed.
Lemma lem3621292 {A B C : Type'} (x'' : B) (x : C) (h : B -> C) (f : A -> B) (x''' : A) : ((term324 B C x h x'') = (term325 A B C x h f x''')) = ((term324 B C x h x'') = (x = (term44 A B C h f x'''))).
Proof. exact (MK_COMB (@lem3621291 B C x h x'') (@lem3621290 A B C x h f x''')). Qed.
Lemma lem3621293 {B C : Type'} (x : C) (h : B -> C) (x'' : B) : (term324 B C x h x'') = (x = (h x'')).
Proof. exact (eq_refl (term324 B C x h x'')). Qed.
Lemma lem3621294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3621295 {B C : Type'} (x : C) (h : B -> C) (x'' : B) : (term326 B C x h x'') = (term327 B C x h x'').
Proof. exact (MK_COMB (@lem3621294) (@lem3621293 B C x h x'')). Qed.
Lemma lem3621296 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (x''' : A) : (x = (term44 A B C h f x''')) = (x = (term44 A B C h f x''')).
Proof. exact (eq_refl (x = (term44 A B C h f x'''))). Qed.
Lemma lem3621297 {A B C : Type'} (x'' : B) (x : C) (h : B -> C) (f : A -> B) (x''' : A) : ((term324 B C x h x'') = (x = (term44 A B C h f x'''))) = ((x = (h x'')) = (x = (term44 A B C h f x'''))).
Proof. exact (MK_COMB (@lem3621295 B C x h x'') (@lem3621296 A B C x h f x''')). Qed.
Lemma lem3621298 {A B C : Type'} (x'' : B) (x : C) (h : B -> C) (f : A -> B) (x''' : A) : ((term324 B C x h x'') = (term325 A B C x h f x''')) = ((x = (h x'')) = (x = (term44 A B C h f x'''))).
Proof. exact (TRANS (@lem3621292 A B C x'' x h f x''') (@lem3621297 A B C x'' x h f x''')). Qed.
Lemma lem3621299 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : (x = (h x'')) = (x = (term44 A B C h f x''')).
Proof. exact (EQ_MP (@lem3621298 A B C x'' x h f x''') (@lem3621289 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621300 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : x = (term44 A B C h f x''').
Proof. exact (EQ_MP (@lem3621299 A B C g x h x'' f s x''' h1) (@lem3621130 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621342 {A B C : Type'} (_39331 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term142 A B C s g h f _39331.
Proof. exact (EQ_MP (@lem3621058 A B C s g h f _39331) (@lem3621057 A B C _39331 g h f s t h1)). Qed.
Lemma lem3621371 {A C : Type'} (g : A -> C) (s : A -> Prop) (_39334 : A) : (term328 A C g s _39334) = (term328 A C g s _39334).
Proof. exact (eq_refl (term328 A C g s _39334)). Qed.
Lemma lem3621372 {A B C : Type'} (_39334 : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : (term329 A C g s _39334 x) = (term330 A B C g s _39334 h f x''').
Proof. exact (MK_COMB (@lem3621371 A C g s _39334) (@lem3621300 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621373 {A B C : Type'} (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term330 A B C g s _39334 h f x''') = (term331 A B C h f x''' g s _39334).
Proof. exact (eq_refl (term330 A B C g s _39334 h f x''')). Qed.
Lemma lem3621374 {A C : Type'} (g : A -> C) (s : A -> Prop) (_39334 : A) (x : C) : (term332 A C g s _39334 x) = (term332 A C g s _39334 x).
Proof. exact (eq_refl (term332 A C g s _39334 x)). Qed.
Lemma lem3621375 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : ((term329 A C g s _39334 x) = (term330 A B C g s _39334 h f x''')) = ((term329 A C g s _39334 x) = (term331 A B C h f x''' g s _39334)).
Proof. exact (MK_COMB (@lem3621374 A C g s _39334 x) (@lem3621373 A B C h f x''' g s _39334)). Qed.
Lemma lem3621376 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term329 A C g s _39334 x) = (term146 A C x g s _39334).
Proof. exact (eq_refl (term329 A C g s _39334 x)). Qed.
Lemma lem3621377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3621378 {A C : Type'} (x : C) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term332 A C g s _39334 x) = (term333 A C x g s _39334).
Proof. exact (MK_COMB (@lem3621377) (@lem3621376 A C x g s _39334)). Qed.
Lemma lem3621379 {A B C : Type'} (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term331 A B C h f x''' g s _39334) = (term331 A B C h f x''' g s _39334).
Proof. exact (eq_refl (term331 A B C h f x''' g s _39334)). Qed.
Lemma lem3621380 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : ((term329 A C g s _39334 x) = (term331 A B C h f x''' g s _39334)) = ((term146 A C x g s _39334) = (term331 A B C h f x''' g s _39334)).
Proof. exact (MK_COMB (@lem3621378 A C x g s _39334) (@lem3621379 A B C h f x''' g s _39334)). Qed.
Lemma lem3621381 {A B C : Type'} (x : C) (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : ((term329 A C g s _39334 x) = (term330 A B C g s _39334 h f x''')) = ((term146 A C x g s _39334) = (term331 A B C h f x''' g s _39334)).
Proof. exact (TRANS (@lem3621375 A B C x h f x''' g s _39334) (@lem3621380 A B C x h f x''' g s _39334)). Qed.
Lemma lem3621382 {A B C : Type'} (_39334 : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : (term146 A C x g s _39334) = (term331 A B C h f x''' g s _39334).
Proof. exact (EQ_MP (@lem3621381 A B C x h f x''' g s _39334) (@lem3621372 A B C _39334 g x h x'' f s x''' h1)). Qed.
Lemma lem3621383 {A B C : Type'} (_39334 : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term331 A B C h f x''' g s _39334.
Proof. exact (EQ_MP (@lem3621382 A B C _39334 g x h x'' f s x''' h1) (@lem3621287 A B C _39334 g x h x'' f s x''' h1)). Qed.
Lemma lem3621474 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : s x'.
Proof. exact (proj2 (@lem3620826 A B C g x' x h f s h1)). Qed.
Lemma lem3621475 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term334 A s x'.
Proof. exact (fun h0 : term335 A s x' => @lem3621474 A B C g x' x h f s h1). Qed.
Lemma lem3621477 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621478 {A : Type'} (s : A -> Prop) (x' : A) : (term334 A s x') = (s x').
Proof. exact (@lem3621477 (s x')). Qed.
Lemma lem3621479 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : s x'.
Proof. exact (EQ_MP (@lem3621478 A s x') (@lem3621475 A B C g x' x h f s h1)). Qed.
Lemma lem3621485 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3621486 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : (term142 A B C s g h f _39326) = (term337 A B C g h f s _39326).
Proof. exact (@lem3621485 ((g _39326) = (term44 A B C h f _39326)) (term335 A s _39326)). Qed.
Lemma lem3621494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3621495 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : (term338 A B C s g h f _39326) = (term339 A B C g h f s _39326).
Proof. exact (MK_COMB (@lem3621494) (@lem3621486 A B C g h f s _39326)). Qed.
Lemma lem3621503 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : (term337 A B C g h f s _39326) = (term337 A B C g h f s _39326).
Proof. exact (eq_refl (term337 A B C g h f s _39326)). Qed.
Lemma lem3621504 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : ((term142 A B C s g h f _39326) = (term337 A B C g h f s _39326)) = ((term337 A B C g h f s _39326) = (term337 A B C g h f s _39326)).
Proof. exact (MK_COMB (@lem3621495 A B C g h f s _39326) (@lem3621503 A B C g h f s _39326)). Qed.
Lemma lem3621506 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3621507 (x : Prop) : (x = x) = True.
Proof. exact (@lem3621506 Prop x). Qed.
Lemma lem3621508 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : ((term337 A B C g h f s _39326) = (term337 A B C g h f s _39326)) = True.
Proof. exact (@lem3621507 (term337 A B C g h f s _39326)). Qed.
Lemma lem3621509 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : ((term142 A B C s g h f _39326) = (term337 A B C g h f s _39326)) = True.
Proof. exact (TRANS (@lem3621504 A B C g h f s _39326) (@lem3621508 A B C g h f s _39326)). Qed.
Lemma lem3621510 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : True = ((term142 A B C s g h f _39326) = (term337 A B C g h f s _39326)).
Proof. exact (SYM (@lem3621509 A B C g h f s _39326)). Qed.
Lemma lem3621511 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39326 : A) : (term142 A B C s g h f _39326) = (term337 A B C g h f s _39326).
Proof. exact (EQ_MP (@lem3621510 A B C g h f s _39326) (@lem0)). Qed.
Lemma lem3621512 {A B C : Type'} (_39326 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term337 A B C g h f s _39326.
Proof. exact (EQ_MP (@lem3621511 A B C g h f s _39326) (@lem3621162 A B C _39326 g h f s t h1)). Qed.
Lemma lem3621514 (b : Prop) (a : Prop) : (a \/ b) = (term340 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3621515 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39326 : A) : (term337 A B C g h f s _39326) = (term341 A B C s g h f _39326).
Proof. exact (@lem3621514 (term335 A s _39326) ((g _39326) = (term44 A B C h f _39326))). Qed.
Lemma lem3621517 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3621518 {A : Type'} (s : A -> Prop) (_39326 : A) : (term342 A s _39326) = (s _39326).
Proof. exact (@lem3621517 (s _39326)). Qed.
Lemma lem3621519 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3621520 {A : Type'} (s : A -> Prop) (_39326 : A) : (term343 A s _39326) = (term76 A s _39326).
Proof. exact (MK_COMB (@lem3621519) (@lem3621518 A s _39326)). Qed.
Lemma lem3621521 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (_39326 : A) : ((g _39326) = (term44 A B C h f _39326)) = ((g _39326) = (term44 A B C h f _39326)).
Proof. exact (eq_refl ((g _39326) = (term44 A B C h f _39326))). Qed.
Lemma lem3621522 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39326 : A) : (term341 A B C s g h f _39326) = (term77 A B C s g h f _39326).
Proof. exact (MK_COMB (@lem3621520 A s _39326) (@lem3621521 A B C g h f _39326)). Qed.
Lemma lem3621523 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39326 : A) : (term337 A B C g h f s _39326) = (term77 A B C s g h f _39326).
Proof. exact (TRANS (@lem3621515 A B C s g h f _39326) (@lem3621522 A B C s g h f _39326)). Qed.
Lemma lem3621526 {A B C : Type'} (_39326 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term77 A B C s g h f _39326.
Proof. exact (EQ_MP (@lem3621523 A B C s g h f _39326) (@lem3621512 A B C _39326 g h f s t h1)). Qed.
Lemma lem3621527 {A B C : Type'} (_39326 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term77 A B C s g h f _39326.
Proof. exact (@lem3621526 A B C _39326 g h f s t h1). Qed.
Lemma lem3621528 {A B C : Type'} (x' : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term77 A B C s g h f x'.
Proof. exact (@lem3621527 A B C x' g h f s t h1). Qed.
Lemma lem3621531 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term97 A B C g h f s t) (h2 : term199 A B C g x' x h f s) : (g x') = (term44 A B C h f x').
Proof. exact (@lem3621528 A B C x' g h f s t h1 (@lem3621479 A B C g x' x h f s h2)). Qed.
Lemma lem3621532 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term97 A B C g h f s t) (h2 : term199 A B C g x' x h f s) : term344 A B C g h f x'.
Proof. exact (fun h0 : term345 A B C g h f x' => @lem3621531 A B C t g x' x h f s h1 h2). Qed.
Lemma lem3621534 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621535 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (x' : A) : (term344 A B C g h f x') = ((g x') = (term44 A B C h f x')).
Proof. exact (@lem3621534 ((g x') = (term44 A B C h f x'))). Qed.
Lemma lem3621536 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term97 A B C g h f s t) (h2 : term199 A B C g x' x h f s) : (g x') = (term44 A B C h f x').
Proof. exact (EQ_MP (@lem3621535 A B C g h f x') (@lem3621532 A B C t g x' x h f s h1 h2)). Qed.
Lemma lem3621538 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3621539 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3621538 B x). Qed.
Lemma lem3621540 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (@lem3621539 B (f x')). Qed.
Lemma lem3621541 {A B : Type'} (f : A -> B) (x' : A) : term346 A B f x'.
Proof. exact (fun h0 : term347 A B f x' => @lem3621540 A B f x'). Qed.
Lemma lem3621543 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621544 {A B : Type'} (f : A -> B) (x' : A) : (term346 A B f x') = ((f x') = (f x')).
Proof. exact (@lem3621543 ((f x') = (f x'))). Qed.
Lemma lem3621545 {A B : Type'} (f : A -> B) (x' : A) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3621544 A B f x') (@lem3621541 A B f x')). Qed.
Lemma lem3621547 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : s x'.
Proof. exact (proj2 (@lem3620826 A B C g x' x h f s h1)). Qed.
Lemma lem3621548 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term334 A s x'.
Proof. exact (fun h0 : term335 A s x' => @lem3621547 A B C g x' x h f s h1). Qed.
Lemma lem3621550 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621551 {A : Type'} (s : A -> Prop) (x' : A) : (term334 A s x') = (s x').
Proof. exact (@lem3621550 (s x')). Qed.
Lemma lem3621552 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : s x'.
Proof. exact (EQ_MP (@lem3621551 A s x') (@lem3621548 A B C g x' x h f s h1)). Qed.
Lemma lem3621554 (a : Prop) (b : Prop) : (term348 a b) = (term349 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3621555 {A B : Type'} (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term146 A B _39329 f s _39330) = (term145 A B _39329 f s _39330).
Proof. exact (@lem3621554 (_39329 = (f _39330)) (s _39330)). Qed.
Lemma lem3621556 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) : (term350 A B C g x' h _39329) = (term350 A B C g x' h _39329).
Proof. exact (eq_refl (term350 A B C g x' h _39329)). Qed.
Lemma lem3621557 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term320 A B C g x' h _39329 f s _39330) = (term351 A B C g x' h _39329 f s _39330).
Proof. exact (MK_COMB (@lem3621556 A B C g x' h _39329) (@lem3621555 A B _39329 f s _39330)). Qed.
Lemma lem3621559 (a : Prop) (b : Prop) : (term348 a b) = (term349 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3621560 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term351 A B C g x' h _39329 f s _39330) = (term352 A B C g x' h _39329 f s _39330).
Proof. exact (@lem3621559 ((g x') = (h _39329)) (term85 A B _39329 f s _39330)). Qed.
Lemma lem3621561 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term320 A B C g x' h _39329 f s _39330) = (term352 A B C g x' h _39329 f s _39330).
Proof. exact (TRANS (@lem3621557 A B C g x' h _39329 f s _39330) (@lem3621560 A B C g x' h _39329 f s _39330)). Qed.
Lemma lem3621563 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3621564 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term352 A B C g x' h _39329 f s _39330) = (term353 A B C g x' h _39329 f s _39330).
Proof. exact (@lem3621563 (term354 A B C g x' h _39329 f s _39330)). Qed.
Lemma lem3621565 {A B C : Type'} (g : A -> C) (x' : A) (h : B -> C) (_39329 : B) (f : A -> B) (s : A -> Prop) (_39330 : A) : (term320 A B C g x' h _39329 f s _39330) = (term353 A B C g x' h _39329 f s _39330).
Proof. exact (TRANS (@lem3621561 A B C g x' h _39329 f s _39330) (@lem3621564 A B C g x' h _39329 f s _39330)). Qed.
Lemma lem3621567 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term355 A B f s x'.
Proof. exact (conj (@lem3621545 A B f x') (@lem3621552 A B C g x' x h f s h1)). Qed.
Lemma lem3621568 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term97 A B C g h f s t) (h2 : term199 A B C g x' x h f s) : term356 A B C g h f s x'.
Proof. exact (conj (@lem3621536 A B C t g x' x h f s h1 h2) (@lem3621567 A B C g x' x h f s h2)). Qed.
Lemma lem3621570 {A B C : Type'} (_39329 : B) (_39330 : A) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term353 A B C g x' h _39329 f s _39330.
Proof. exact (EQ_MP (@lem3621565 A B C g x' h _39329 f s _39330) (@lem3621203 A B C _39329 _39330 g x' x h f s h1)). Qed.
Lemma lem3621571 {A B C : Type'} (_39329 : B) (_39330 : A) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term353 A B C g x' h _39329 f s _39330.
Proof. exact (@lem3621570 A B C _39329 _39330 g x' x h f s h1). Qed.
Lemma lem3621572 {A B C : Type'} (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term199 A B C g x' x h f s) : term357 A B C g h f s x'.
Proof. exact (@lem3621571 A B C (f x') x' g x' x h f s h1). Qed.
Lemma lem3621575 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term97 A B C g h f s t) (h2 : term199 A B C g x' x h f s) : False.
Proof. exact (@lem3621572 A B C g x' x h f s h2 (@lem3621568 A B C t g x' x h f s h1 h2)). Qed.
Lemma lem3621576 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term97 A B C g h f s t) (h2 : term199 A B C g x' x h f s) : term358.
Proof. exact (fun h0 : ~ False => @lem3621575 A B C t g x' x h f s h1 h2). Qed.
Lemma lem3621578 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621579 : term358 = False.
Proof. exact (@lem3621578 False). Qed.
Lemma lem3621649 {C : Type'} (x : C) (y : C) (z : C) : term359 C x y z.
Proof. exact (@lem21385 C x y z). Qed.
Lemma lem3621657 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : s x'''.
Proof. exact (proj2 (@lem3620831 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621658 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term334 A s x'''.
Proof. exact (fun h0 : term335 A s x''' => @lem3621657 A B C g x h x'' f s x''' h1). Qed.
Lemma lem3621660 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621661 {A : Type'} (s : A -> Prop) (x''' : A) : (term334 A s x''') = (s x''').
Proof. exact (@lem3621660 (s x''')). Qed.
Lemma lem3621662 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : s x'''.
Proof. exact (EQ_MP (@lem3621661 A s x''') (@lem3621658 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621668 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3621669 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : (term142 A B C s g h f _39331) = (term337 A B C g h f s _39331).
Proof. exact (@lem3621668 ((g _39331) = (term44 A B C h f _39331)) (term335 A s _39331)). Qed.
Lemma lem3621677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3621678 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : (term338 A B C s g h f _39331) = (term339 A B C g h f s _39331).
Proof. exact (MK_COMB (@lem3621677) (@lem3621669 A B C g h f s _39331)). Qed.
Lemma lem3621686 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : (term337 A B C g h f s _39331) = (term337 A B C g h f s _39331).
Proof. exact (eq_refl (term337 A B C g h f s _39331)). Qed.
Lemma lem3621687 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : ((term142 A B C s g h f _39331) = (term337 A B C g h f s _39331)) = ((term337 A B C g h f s _39331) = (term337 A B C g h f s _39331)).
Proof. exact (MK_COMB (@lem3621678 A B C g h f s _39331) (@lem3621686 A B C g h f s _39331)). Qed.
Lemma lem3621689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3621690 (x : Prop) : (x = x) = True.
Proof. exact (@lem3621689 Prop x). Qed.
Lemma lem3621691 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : ((term337 A B C g h f s _39331) = (term337 A B C g h f s _39331)) = True.
Proof. exact (@lem3621690 (term337 A B C g h f s _39331)). Qed.
Lemma lem3621692 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : ((term142 A B C s g h f _39331) = (term337 A B C g h f s _39331)) = True.
Proof. exact (TRANS (@lem3621687 A B C g h f s _39331) (@lem3621691 A B C g h f s _39331)). Qed.
Lemma lem3621693 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : True = ((term142 A B C s g h f _39331) = (term337 A B C g h f s _39331)).
Proof. exact (SYM (@lem3621692 A B C g h f s _39331)). Qed.
Lemma lem3621694 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (_39331 : A) : (term142 A B C s g h f _39331) = (term337 A B C g h f s _39331).
Proof. exact (EQ_MP (@lem3621693 A B C g h f s _39331) (@lem0)). Qed.
Lemma lem3621695 {A B C : Type'} (_39331 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term337 A B C g h f s _39331.
Proof. exact (EQ_MP (@lem3621694 A B C g h f s _39331) (@lem3621342 A B C _39331 g h f s t h1)). Qed.
Lemma lem3621697 (b : Prop) (a : Prop) : (a \/ b) = (term340 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3621698 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39331 : A) : (term337 A B C g h f s _39331) = (term341 A B C s g h f _39331).
Proof. exact (@lem3621697 (term335 A s _39331) ((g _39331) = (term44 A B C h f _39331))). Qed.
Lemma lem3621700 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3621701 {A : Type'} (s : A -> Prop) (_39331 : A) : (term342 A s _39331) = (s _39331).
Proof. exact (@lem3621700 (s _39331)). Qed.
Lemma lem3621702 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3621703 {A : Type'} (s : A -> Prop) (_39331 : A) : (term343 A s _39331) = (term76 A s _39331).
Proof. exact (MK_COMB (@lem3621702) (@lem3621701 A s _39331)). Qed.
Lemma lem3621704 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (_39331 : A) : ((g _39331) = (term44 A B C h f _39331)) = ((g _39331) = (term44 A B C h f _39331)).
Proof. exact (eq_refl ((g _39331) = (term44 A B C h f _39331))). Qed.
Lemma lem3621705 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39331 : A) : (term341 A B C s g h f _39331) = (term77 A B C s g h f _39331).
Proof. exact (MK_COMB (@lem3621703 A s _39331) (@lem3621704 A B C g h f _39331)). Qed.
Lemma lem3621706 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (_39331 : A) : (term337 A B C g h f s _39331) = (term77 A B C s g h f _39331).
Proof. exact (TRANS (@lem3621698 A B C s g h f _39331) (@lem3621705 A B C s g h f _39331)). Qed.
Lemma lem3621709 {A B C : Type'} (_39331 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term77 A B C s g h f _39331.
Proof. exact (EQ_MP (@lem3621706 A B C s g h f _39331) (@lem3621695 A B C _39331 g h f s t h1)). Qed.
Lemma lem3621710 {A B C : Type'} (_39331 : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term77 A B C s g h f _39331.
Proof. exact (@lem3621709 A B C _39331 g h f s t h1). Qed.
Lemma lem3621711 {A B C : Type'} (x''' : A) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term77 A B C s g h f x'''.
Proof. exact (@lem3621710 A B C x''' g h f s t h1). Qed.
Lemma lem3621714 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : (g x''') = (term44 A B C h f x''').
Proof. exact (@lem3621711 A B C x''' g h f s t h1 (@lem3621662 A B C g x h x'' f s x''' h2)). Qed.
Lemma lem3621715 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : term344 A B C g h f x'''.
Proof. exact (fun h0 : term345 A B C g h f x''' => @lem3621714 A B C t g x h x'' f s x''' h1 h2). Qed.
Lemma lem3621717 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621718 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (x''' : A) : (term344 A B C g h f x''') = ((g x''') = (term44 A B C h f x''')).
Proof. exact (@lem3621717 ((g x''') = (term44 A B C h f x'''))). Qed.
Lemma lem3621719 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : (g x''') = (term44 A B C h f x''').
Proof. exact (EQ_MP (@lem3621718 A B C g h f x''') (@lem3621715 A B C t g x h x'' f s x''' h1 h2)). Qed.
Lemma lem3621721 {C : Type'} (x : C) : x = x.
Proof. exact (@lem21386 C x). Qed.
Lemma lem3621722 {C : Type'} (x : C) : x = x.
Proof. exact (@lem3621721 C x). Qed.
Lemma lem3621723 {A C : Type'} (g : A -> C) (x''' : A) : (g x''') = (g x''').
Proof. exact (@lem3621722 C (g x''')). Qed.
Lemma lem3621724 {A C : Type'} (g : A -> C) (x''' : A) : term346 A C g x'''.
Proof. exact (fun h0 : term347 A C g x''' => @lem3621723 A C g x'''). Qed.
Lemma lem3621726 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621727 {A C : Type'} (g : A -> C) (x''' : A) : (term346 A C g x''') = ((g x''') = (g x''')).
Proof. exact (@lem3621726 ((g x''') = (g x'''))). Qed.
Lemma lem3621728 {A C : Type'} (g : A -> C) (x''' : A) : (g x''') = (g x''').
Proof. exact (EQ_MP (@lem3621727 A C g x''') (@lem3621724 A C g x''')). Qed.
Lemma lem3621746 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3621747 {C : Type'} (y : C) (x : C) (z : C) : (term360 C x y z) = (term361 C y x z).
Proof. exact (@lem3621746 (y = z) (term362 C x z)). Qed.
Lemma lem3621757 {C : Type'} (x : C) (y : C) : (term363 C x y) = (term363 C x y).
Proof. exact (eq_refl (term363 C x y)). Qed.
Lemma lem3621758 {C : Type'} (y : C) (x : C) (z : C) : (term359 C x y z) = (term364 C y x z).
Proof. exact (MK_COMB (@lem3621757 C x y) (@lem3621747 C y x z)). Qed.
Lemma lem3621762 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3621763 {C : Type'} (y : C) (x : C) (z : C) : (term364 C y x z) = (term365 C y x z).
Proof. exact (@lem3621762 (y = z) (term362 C x y) (term362 C x z)). Qed.
Lemma lem3621785 {C : Type'} (y : C) (x : C) (z : C) : (term359 C x y z) = (term365 C y x z).
Proof. exact (TRANS (@lem3621758 C y x z) (@lem3621763 C y x z)). Qed.
Lemma lem3621786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3621787 {C : Type'} (y : C) (x : C) (z : C) : (term366 C x y z) = (term367 C y x z).
Proof. exact (MK_COMB (@lem3621786) (@lem3621785 C y x z)). Qed.
Lemma lem3621809 {C : Type'} (y : C) (x : C) (z : C) : (term365 C y x z) = (term365 C y x z).
Proof. exact (eq_refl (term365 C y x z)). Qed.
Lemma lem3621810 {C : Type'} (y : C) (x : C) (z : C) : ((term359 C x y z) = (term365 C y x z)) = ((term365 C y x z) = (term365 C y x z)).
Proof. exact (MK_COMB (@lem3621787 C y x z) (@lem3621809 C y x z)). Qed.
Lemma lem3621812 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3621813 (x : Prop) : (x = x) = True.
Proof. exact (@lem3621812 Prop x). Qed.
Lemma lem3621814 {C : Type'} (y : C) (x : C) (z : C) : ((term365 C y x z) = (term365 C y x z)) = True.
Proof. exact (@lem3621813 (term365 C y x z)). Qed.
Lemma lem3621815 {C : Type'} (y : C) (x : C) (z : C) : ((term359 C x y z) = (term365 C y x z)) = True.
Proof. exact (TRANS (@lem3621810 C y x z) (@lem3621814 C y x z)). Qed.
Lemma lem3621816 {C : Type'} (y : C) (x : C) (z : C) : True = ((term359 C x y z) = (term365 C y x z)).
Proof. exact (SYM (@lem3621815 C y x z)). Qed.
Lemma lem3621817 {C : Type'} (y : C) (x : C) (z : C) : (term359 C x y z) = (term365 C y x z).
Proof. exact (EQ_MP (@lem3621816 C y x z) (@lem0)). Qed.
Lemma lem3621818 {C : Type'} (y : C) (x : C) (z : C) : term365 C y x z.
Proof. exact (EQ_MP (@lem3621817 C y x z) (@lem3621649 C x y z)). Qed.
Lemma lem3621820 (b : Prop) (a : Prop) : (a \/ b) = (term340 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3621821 {C : Type'} (x : C) (y : C) (z : C) : (term365 C y x z) = (term368 C x y z).
Proof. exact (@lem3621820 (term369 C y x z) (y = z)). Qed.
Lemma lem3621823 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3621824 {C : Type'} (y : C) (x : C) (z : C) : (term372 C y x z) = (term373 C y x z).
Proof. exact (@lem3621823 (term362 C x y) (term362 C x z)). Qed.
Lemma lem3621826 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3621827 {C : Type'} (x : C) (y : C) : (term374 C x y) = (x = y).
Proof. exact (@lem3621826 (x = y)). Qed.
Lemma lem3621828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3621829 {C : Type'} (x : C) (y : C) : (term375 C x y) = (term376 C x y).
Proof. exact (MK_COMB (@lem3621828) (@lem3621827 C x y)). Qed.
Lemma lem3621831 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3621832 {C : Type'} (x : C) (z : C) : (term374 C x z) = (x = z).
Proof. exact (@lem3621831 (x = z)). Qed.
Lemma lem3621833 {C : Type'} (y : C) (x : C) (z : C) : (term373 C y x z) = (term377 C y x z).
Proof. exact (MK_COMB (@lem3621829 C x y) (@lem3621832 C x z)). Qed.
Lemma lem3621834 {C : Type'} (y : C) (x : C) (z : C) : (term372 C y x z) = (term377 C y x z).
Proof. exact (TRANS (@lem3621824 C y x z) (@lem3621833 C y x z)). Qed.
Lemma lem3621835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3621836 {C : Type'} (y : C) (x : C) (z : C) : (term378 C y x z) = (term379 C y x z).
Proof. exact (MK_COMB (@lem3621835) (@lem3621834 C y x z)). Qed.
Lemma lem3621837 {C : Type'} (y : C) (z : C) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3621838 {C : Type'} (x : C) (y : C) (z : C) : (term368 C x y z) = (term380 C x y z).
Proof. exact (MK_COMB (@lem3621836 C y x z) (@lem3621837 C y z)). Qed.
Lemma lem3621839 {C : Type'} (x : C) (y : C) (z : C) : (term365 C y x z) = (term380 C x y z).
Proof. exact (TRANS (@lem3621821 C x y z) (@lem3621838 C x y z)). Qed.
Lemma lem3621841 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : term381 A B C h f g x'''.
Proof. exact (conj (@lem3621719 A B C t g x h x'' f s x''' h1 h2) (@lem3621728 A C g x''')). Qed.
Lemma lem3621843 {C : Type'} (x : C) (y : C) (z : C) : term380 C x y z.
Proof. exact (EQ_MP (@lem3621839 C x y z) (@lem3621818 C y x z)). Qed.
Lemma lem3621844 {C : Type'} (x : C) (y : C) (z : C) : term380 C x y z.
Proof. exact (@lem3621843 C x y z). Qed.
Lemma lem3621845 {A B C : Type'} (h : B -> C) (f : A -> B) (g : A -> C) (x''' : A) : term382 A B C h f g x'''.
Proof. exact (@lem3621844 C (g x''') (term44 A B C h f x''') (g x''')). Qed.
Lemma lem3621848 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : (term44 A B C h f x''') = (g x''').
Proof. exact (@lem3621845 A B C h f g x''' (@lem3621841 A B C t g x h x'' f s x''' h1 h2)). Qed.
Lemma lem3621849 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : term383 A B C h f g x'''.
Proof. exact (fun h0 : term384 A B C h f g x''' => @lem3621848 A B C t g x h x'' f s x''' h1 h2). Qed.
Lemma lem3621851 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621852 {A B C : Type'} (h : B -> C) (f : A -> B) (g : A -> C) (x''' : A) : (term383 A B C h f g x''') = ((term44 A B C h f x''') = (g x''')).
Proof. exact (@lem3621851 ((term44 A B C h f x''') = (g x'''))). Qed.
Lemma lem3621853 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : (term44 A B C h f x''') = (g x''').
Proof. exact (EQ_MP (@lem3621852 A B C h f g x''') (@lem3621849 A B C t g x h x'' f s x''' h1 h2)). Qed.
Lemma lem3621855 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : s x'''.
Proof. exact (proj2 (@lem3620831 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621856 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term334 A s x'''.
Proof. exact (fun h0 : term335 A s x''' => @lem3621855 A B C g x h x'' f s x''' h1). Qed.
Lemma lem3621858 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621859 {A : Type'} (s : A -> Prop) (x''' : A) : (term334 A s x''') = (s x''').
Proof. exact (@lem3621858 (s x''')). Qed.
Lemma lem3621860 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : s x'''.
Proof. exact (EQ_MP (@lem3621859 A s x''') (@lem3621856 A B C g x h x'' f s x''' h1)). Qed.
Lemma lem3621862 (a : Prop) (b : Prop) : (term348 a b) = (term349 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3621863 {A B C : Type'} (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term331 A B C h f x''' g s _39334) = (term385 A B C h f x''' g s _39334).
Proof. exact (@lem3621862 ((term44 A B C h f x''') = (g _39334)) (s _39334)). Qed.
Lemma lem3621865 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3621866 {A B C : Type'} (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term385 A B C h f x''' g s _39334) = (term386 A B C h f x''' g s _39334).
Proof. exact (@lem3621865 (term387 A B C h f x''' g s _39334)). Qed.
Lemma lem3621867 {A B C : Type'} (h : B -> C) (f : A -> B) (x''' : A) (g : A -> C) (s : A -> Prop) (_39334 : A) : (term331 A B C h f x''' g s _39334) = (term386 A B C h f x''' g s _39334).
Proof. exact (TRANS (@lem3621863 A B C h f x''' g s _39334) (@lem3621866 A B C h f x''' g s _39334)). Qed.
Lemma lem3621869 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : term388 A B C h f g s x'''.
Proof. exact (conj (@lem3621853 A B C t g x h x'' f s x''' h1 h2) (@lem3621860 A B C g x h x'' f s x''' h2)). Qed.
Lemma lem3621871 {A B C : Type'} (_39334 : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term386 A B C h f x''' g s _39334.
Proof. exact (EQ_MP (@lem3621867 A B C h f x''' g s _39334) (@lem3621383 A B C _39334 g x h x'' f s x''' h1)). Qed.
Lemma lem3621872 {A B C : Type'} (_39334 : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term386 A B C h f x''' g s _39334.
Proof. exact (@lem3621871 A B C _39334 g x h x'' f s x''' h1). Qed.
Lemma lem3621873 {A B C : Type'} (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term238 A B C g x h x'' f s x''') : term389 A B C h f g s x'''.
Proof. exact (@lem3621872 A B C x''' g x h x'' f s x''' h1). Qed.
Lemma lem3621876 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : False.
Proof. exact (@lem3621873 A B C g x h x'' f s x''' h2 (@lem3621869 A B C t g x h x'' f s x''' h1 h2)). Qed.
Lemma lem3621877 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : term358.
Proof. exact (fun h0 : ~ False => @lem3621876 A B C t g x h x'' f s x''' h1 h2). Qed.
Lemma lem3621879 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3621880 : term358 = False.
Proof. exact (@lem3621879 False). Qed.
Lemma lem3621883 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term238 A B C g x h x'' f s x''') : False.
Proof. exact (EQ_MP (@lem3621880) (@lem3621877 A B C t g x h x'' f s x''' h1 h2)). Qed.
Lemma lem3621884 {A B C : Type'} (t : B -> Prop) (g : A -> C) (x' : A) (x : C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term97 A B C g h f s t) (h2 : term199 A B C g x' x h f s) : False.
Proof. exact (EQ_MP (@lem3621579) (@lem3621576 A B C t g x' x h f s h1 h2)). Qed.
Lemma lem3621885 {A B C : Type'} (t : B -> Prop) (x' : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term284 A B C x' g x h x'' f s x''') : False.
Proof. exact (or_elim (@lem3620818 A B C x' g x h x'' f s x''' h2) (fun h0 : term199 A B C g x' x h f s => @lem3621884 A B C t g x' x h f s h1 h0) (fun h0 : term238 A B C g x h x'' f s x''' => @lem3621883 A B C t g x h x'' f s x''' h1 h0)). Qed.
Lemma lem3621886 {A B C : Type'} (t : B -> Prop) (x' : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term284 A B C x' g x h x'' f s x''') : (term284 A B C x' g x h x'' f s x''') = False.
Proof. exact (prop_ext (fun h3 : term284 A B C x' g x h x'' f s x''' => @lem3621885 A B C t x' g x h x'' f s x''' h1 h2) (fun h3 : False => @lem3620818 A B C x' g x h x'' f s x''' h2)). Qed.
Lemma lem3621887 {A B C : Type'} (t : B -> Prop) (x' : A) (g : A -> C) (x : C) (h : B -> C) (x'' : B) (f : A -> B) (s : A -> Prop) (x''' : A) (h1 : term97 A B C g h f s t) (h2 : term284 A B C x' g x h x'' f s x''') : False.
Proof. exact (EQ_MP (@lem3621886 A B C t x' g x h x'' f s x''' h1 h2) (@lem3620818 A B C x' g x h x'' f s x''' h2)). Qed.
Lemma lem3621888 {A B C : Type'} (x' : A) (x : C) (x'' : B) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term287 A B C x' g x h x'' f s) (h2 : term97 A B C g h f s t) : False.
Proof. exact (ex_elim (@lem3620650 A B C x' g x h x'' f s h1) (fun x''' : A => fun h0 : term286 A B C x' g x h x'' f s x''' => @lem3621887 A B C t x' g x h x'' f s x''' h2 h0)). Qed.
Lemma lem3621889 {A B C : Type'} (x' : A) (x : C) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term289 A B C x' g x h f s) (h2 : term97 A B C g h f s t) : False.
Proof. exact (ex_elim (@lem3620649 A B C x' g x h f s h1) (fun x'' : B => fun h0 : term288 A B C x' g x h f s x'' => @lem3621888 A B C x' x x'' g h f s t h0 h2)). Qed.
Lemma lem3621890 {A B C : Type'} (x : C) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term141 A B C g x h f s) (h2 : term97 A B C g h f s t) : False.
Proof. exact (ex_elim (@lem3620648 A B C g x h f s h1) (fun x' : A => fun h0 : term290 A B C g x h f s x' => @lem3621889 A B C x' x g h f s t h0 h2)). Qed.
Lemma lem3621891 {A B C : Type'} (x : C) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term141 A B C g x h f s) (h2 : term97 A B C g h f s t) : (term141 A B C g x h f s) = False.
Proof. exact (prop_ext (fun h3 : term141 A B C g x h f s => @lem3621890 A B C x g h f s t h1 h2) (fun h3 : False => @lem3619956 A B C g x h f s h1)). Qed.
Lemma lem3621892 {A B C : Type'} (x : C) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term141 A B C g x h f s) (h2 : term97 A B C g h f s t) : False.
Proof. exact (EQ_MP (@lem3621891 A B C x g h f s t h1 h2) (@lem3619956 A B C g x h f s h1)). Qed.
Lemma lem3621893 {A B C : Type'} (x : C) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term140 A B C g x h f s.
Proof. exact (fun h0 : term141 A B C g x h f s => @lem3621892 A B C x g h f s t h0 h1). Qed.
Lemma lem3621894 {A B C : Type'} (x : C) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : (term88 A C x g s) = (term107 A B C x h f s).
Proof. exact (EQ_MP (@lem3619955 A B C g x h f s) (@lem3621893 A B C x g h f s t h1)). Qed.
Lemma lem3621899 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term97 A B C g h f s t) : term110 A B C g h f s.
Proof. exact (fun x : C => @lem3621894 A B C x g h f s t h1). Qed.
Lemma lem3621900 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term111 A B C t g h f s.
Proof. exact (fun h0 : term97 A B C g h f s t => @lem3621899 A B C g h f s t h0). Qed.
Lemma lem3621905 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term123 A B C g h f s.
Proof. exact (fun t : B -> Prop => @lem3621900 A B C t g h f s). Qed.
Lemma lem3621910 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : term127 A B C h f s.
Proof. exact (fun g : A -> C => @lem3621905 A B C g h f s). Qed.
Lemma lem3621915 {A B C : Type'} (f : A -> B) (s : A -> Prop) : term131 A B C f s.
Proof. exact (fun h : B -> C => @lem3621910 A B C h f s). Qed.
Lemma lem3621920 {A B C : Type'} (s : A -> Prop) : term135 A B C s.
Proof. exact (fun f : A -> B => @lem3621915 A B C f s). Qed.
Lemma lem3621925 {A B C : Type'} : term139 A B C.
Proof. exact (fun s : A -> Prop => @lem3621920 A B C s). Qed.
Lemma lem3621926 {A B C : Type'} : term138 A B C.
Proof. exact (EQ_MP (@lem3619950 A B C) (@lem3621925 A B C)). Qed.
Lemma lem3621927 {A B C : Type'} (s : A -> Prop) : term390 A B C s.
Proof. exact (@lem3621926 A B C s). Qed.
Lemma lem3621928 {A B C : Type'} (s : A -> Prop) : (term390 A B C s) = (term134 A B C s).
Proof. exact (eq_refl (term390 A B C s)). Qed.
Lemma lem3621929 {A B C : Type'} (s : A -> Prop) : term134 A B C s.
Proof. exact (EQ_MP (@lem3621928 A B C s) (@lem3621927 A B C s)). Qed.
Lemma lem3621930 {A B C : Type'} (s : A -> Prop) (f : A -> B) : term391 A B C s f.
Proof. exact (@lem3621929 A B C s f). Qed.
Lemma lem3621931 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term391 A B C s f) = (term130 A B C f s).
Proof. exact (eq_refl (term391 A B C s f)). Qed.
Lemma lem3621932 {A B C : Type'} (f : A -> B) (s : A -> Prop) : term130 A B C f s.
Proof. exact (EQ_MP (@lem3621931 A B C f s) (@lem3621930 A B C s f)). Qed.
Lemma lem3621933 {A B C : Type'} (f : A -> B) (s : A -> Prop) (h : B -> C) : term392 A B C f s h.
Proof. exact (@lem3621932 A B C f s h). Qed.
Lemma lem3621934 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term392 A B C f s h) = (term126 A B C h f s).
Proof. exact (eq_refl (term392 A B C f s h)). Qed.
Lemma lem3621935 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : term126 A B C h f s.
Proof. exact (EQ_MP (@lem3621934 A B C h f s) (@lem3621933 A B C f s h)). Qed.
Lemma lem3621936 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (g : A -> C) : term393 A B C h f s g.
Proof. exact (@lem3621935 A B C h f s g). Qed.
Lemma lem3621937 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term393 A B C h f s g) = (term122 A B C g h f s).
Proof. exact (eq_refl (term393 A B C h f s g)). Qed.
Lemma lem3621938 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term122 A B C g h f s.
Proof. exact (EQ_MP (@lem3621937 A B C g h f s) (@lem3621936 A B C h f s g)). Qed.
Lemma lem3621939 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term394 A B C g h f s t.
Proof. exact (@lem3621938 A B C g h f s t). Qed.
Lemma lem3621940 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term394 A B C g h f s t) = (term113 A B C t g h f s).
Proof. exact (eq_refl (term394 A B C g h f s t)). Qed.
Lemma lem3621941 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term113 A B C t g h f s.
Proof. exact (EQ_MP (@lem3621940 A B C t g h f s) (@lem3621939 A B C g h f s t)). Qed.
Lemma lem3621943 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term113 A B C t g h f s.
Proof. exact (@lem3619539 A B C t g h f s (@lem3621941 A B C t g h f s)). Qed.
Lemma lem3621944 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term114 A B C t g h f s) : False.
Proof. exact (@lem3621943 A B C t g h f s (@lem3619523 A B C t g h f s h1)). Qed.
Lemma lem3621945 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term114 A B C t g h f s) : (term114 A B C t g h f s) = False.
Proof. exact (prop_ext (fun h2 : term114 A B C t g h f s => @lem3621944 A B C t g h f s h1) (fun h2 : False => @lem3619523 A B C t g h f s h1)). Qed.
Lemma lem3621946 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term114 A B C t g h f s) : False.
Proof. exact (EQ_MP (@lem3621945 A B C t g h f s h1) (@lem3619523 A B C t g h f s h1)). Qed.
Lemma lem3621947 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term113 A B C t g h f s.
Proof. exact (fun h0 : term114 A B C t g h f s => @lem3621946 A B C t g h f s h0). Qed.
Lemma lem3621948 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term111 A B C t g h f s.
Proof. exact (EQ_MP (@lem3619522 A B C t g h f s) (@lem3621947 A B C t g h f s)). Qed.
Lemma lem3621949 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term75 A B C t g h f s.
Proof. exact (EQ_MP (@lem3619518 A B C t g h f s) (@lem3621948 A B C t g h f s)). Qed.
Lemma lem3621950 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term74 A B C t g h f s.
Proof. exact (EQ_MP (@lem3619324 A B C t g h f s) (@lem3621949 A B C t g h f s)). Qed.
Lemma lem3621951 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : (@IMAGE A C g s) = (term54 A B C h f s).
Proof. exact (@lem3621950 A B C t g h f s (@lem3619270 A B C g h f s t h1 h2 h3)). Qed.
Lemma lem3621953 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3621954 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term58 A B C h f s) = (term395 A B C h f s).
Proof. exact (@lem3621953 (term58 A B C h f s)). Qed.
Lemma lem3621955 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term395 A B C h f s) = (term58 A B C h f s).
Proof. exact (SYM (@lem3621954 A B C h f s)). Qed.
Lemma lem3621956 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term396 A B C h f s) : term396 A B C h f s.
Proof. exact (h1). Qed.
Lemma lem3621957 {B : Type'} : term397 B.
Proof. exact (@lem3615104 B B). Qed.
Lemma lem3621958 {B C : Type'} : term398 B C.
Proof. exact (@lem3615104 C B). Qed.
Lemma lem3621959 {A B : Type'} : term399 A B.
Proof. exact (@lem3615104 A B). Qed.
Lemma lem3621960 {A C : Type'} : term399 A C.
Proof. exact (@lem3615104 A C). Qed.
Lemma lem3621962 {B C : Type'} : term399 B C.
Proof. exact (@lem3615104 B C). Qed.
Lemma lem3621963 {B : Type'} : term400 B.
Proof. exact (@lem3599924 B). Qed.
Lemma lem3621964 {C : Type'} : term400 C.
Proof. exact (@lem3599924 C). Qed.
Lemma lem3621965 {A : Type'} : term400 A.
Proof. exact (@lem3599924 A). Qed.
Lemma lem3621969 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term401 A B C t g h f s) : term401 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3621970 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term402 A B C t g h f s.
Proof. exact (fun h0 : term401 A B C t g h f s => @lem3621969 A B C t g h f s h0). Qed.
Lemma lem3621971 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term402 A B C t g h f s) : term402 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3621972 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term401 A B C t g h f s) : term401 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3621973 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term402 A B C t g h f s) (h2 : term401 A B C t g h f s) : term401 A B C t g h f s.
Proof. exact (@lem3621971 A B C t g h f s h1 (@lem3621972 A B C t g h f s h2)). Qed.
Lemma lem3621974 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term401 A B C t g h f s) : term403 A B C t g h f s.
Proof. exact (fun h0 : term402 A B C t g h f s => @lem3621973 A B C t g h f s h0 h1). Qed.
Lemma lem3621975 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term402 A B C t g h f s) : term402 A B C t g h f s.
Proof. exact (h1). Qed.
Lemma lem3621976 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term402 A B C t g h f s) (h2 : term401 A B C t g h f s) : term401 A B C t g h f s.
Proof. exact (@lem3621974 A B C t g h f s h2 (@lem3621975 A B C t g h f s h1)). Qed.
Lemma lem3621977 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term402 A B C t g h f s) : term402 A B C t g h f s.
Proof. exact (fun h0 : term401 A B C t g h f s => @lem3621976 A B C t g h f s h1 h0). Qed.
Lemma lem3621978 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term404 A B C t g h f s.
Proof. exact (fun h0 : term402 A B C t g h f s => @lem3621977 A B C t g h f s h0). Qed.
Lemma lem3621981 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term402 A B C t g h f s.
Proof. exact (@lem3621978 A B C t g h f s (@lem3621970 A B C t g h f s)). Qed.
Lemma lem3621982 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term402 A B C t g h f s.
Proof. exact (@lem3621981 A B C t g h f s). Qed.
Lemma lem3622108 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3622109 {B C : Type'} : (term405 B C) = (term406 B C).
Proof. exact (@lem3622108 (term398 B C)). Qed.
Lemma lem3622120 {B C : Type'} : (term407 B C) = (term407 B C).
Proof. exact (eq_refl (term407 B C)). Qed.
Lemma lem3622121 {B C : Type'} : (term408 B C) = (term409 B C).
Proof. exact (MK_COMB (@lem3622120 B C) (@lem3622109 B C)). Qed.
Lemma lem3622124 {B : Type'} : (term410 B) = (term410 B).
Proof. exact (eq_refl (term410 B)). Qed.
Lemma lem3622125 {B C : Type'} : (term411 B C) = (term412 B C).
Proof. exact (MK_COMB (@lem3622124 B) (@lem3622121 B C)). Qed.
Lemma lem3622128 {A C : Type'} : (term407 A C) = (term407 A C).
Proof. exact (eq_refl (term407 A C)). Qed.
Lemma lem3622129 {A B C : Type'} : (term413 A B C) = (term414 A B C).
Proof. exact (MK_COMB (@lem3622128 A C) (@lem3622125 B C)). Qed.
Lemma lem3622132 {A B : Type'} : (term407 A B) = (term407 A B).
Proof. exact (eq_refl (term407 A B)). Qed.
Lemma lem3622133 {A B C : Type'} : (term415 A B C) = (term416 A B C).
Proof. exact (MK_COMB (@lem3622132 A B) (@lem3622129 A B C)). Qed.
Lemma lem3622136 {C : Type'} : (term417 C) = (term417 C).
Proof. exact (eq_refl (term417 C)). Qed.
Lemma lem3622137 {A B C : Type'} : (term418 A B C) = (term419 A B C).
Proof. exact (MK_COMB (@lem3622136 C) (@lem3622133 A B C)). Qed.
Lemma lem3622140 {B : Type'} : (term417 B) = (term417 B).
Proof. exact (eq_refl (term417 B)). Qed.
Lemma lem3622141 {A B C : Type'} : (term420 A B C) = (term421 A B C).
Proof. exact (MK_COMB (@lem3622140 B) (@lem3622137 A B C)). Qed.
Lemma lem3622144 {A : Type'} : (term417 A) = (term417 A).
Proof. exact (eq_refl (term417 A)). Qed.
Lemma lem3622145 {A B C : Type'} : (term422 A B C) = (term423 A B C).
Proof. exact (MK_COMB (@lem3622144 A) (@lem3622141 A B C)). Qed.
Lemma lem3622148 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term424 A B C h f s) = (term424 A B C h f s).
Proof. exact (eq_refl (term424 A B C h f s)). Qed.
Lemma lem3622149 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term425 A B C h f s) = (term426 A B C h f s).
Proof. exact (MK_COMB (@lem3622148 A B C h f s) (@lem3622145 A B C)). Qed.
Lemma lem3622152 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term427 A B C s g h f) = (term427 A B C s g h f).
Proof. exact (eq_refl (term427 A B C s g h f)). Qed.
Lemma lem3622153 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term428 A B C g h f s) = (term429 A B C g h f s).
Proof. exact (MK_COMB (@lem3622152 A B C s g h f) (@lem3622149 A B C h f s)). Qed.
Lemma lem3622156 {B : Type'} (t : B -> Prop) : (term430 B t) = (term430 B t).
Proof. exact (eq_refl (term430 B t)). Qed.
Lemma lem3622157 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term431 A B C t g h f s) = (term432 A B C t g h f s).
Proof. exact (MK_COMB (@lem3622156 B t) (@lem3622153 A B C g h f s)). Qed.
Lemma lem3622160 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term433 A B f s t) = (term433 A B f s t).
Proof. exact (eq_refl (term433 A B f s t)). Qed.
Lemma lem3622161 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term401 A B C t g h f s) = (term434 A B C t g h f s).
Proof. exact (MK_COMB (@lem3622160 A B f s t) (@lem3622157 A B C t g h f s)). Qed.
Lemma lem3622164 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term435 A B C g h f s) = (term436 A B C g h f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3622161 A B C t g h f s)). Qed.
Lemma lem3622165 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622166 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term437 A B C g h f s) = (term438 A B C g h f s).
Proof. exact (MK_COMB (@lem3622165 B) (@lem3622164 A B C g h f s)). Qed.
Lemma lem3622171 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term439 A B C h f s) = (term440 A B C h f s).
Proof. exact (fun_ext (fun g : A -> C => @lem3622166 A B C g h f s)). Qed.
Lemma lem3622172 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem3622173 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term441 A B C h f s) = (term442 A B C h f s).
Proof. exact (MK_COMB (@lem3622172 A C) (@lem3622171 A B C h f s)). Qed.
Lemma lem3622178 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term443 A B C f s) = (term444 A B C f s).
Proof. exact (fun_ext (fun h : B -> C => @lem3622173 A B C h f s)). Qed.
Lemma lem3622179 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3622180 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term445 A B C f s) = (term446 A B C f s).
Proof. exact (MK_COMB (@lem3622179 B C) (@lem3622178 A B C f s)). Qed.
Lemma lem3622185 {A B C : Type'} (s : A -> Prop) : (term447 A B C s) = (term448 A B C s).
Proof. exact (fun_ext (fun f : A -> B => @lem3622180 A B C f s)). Qed.
Lemma lem3622186 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3622187 {A B C : Type'} (s : A -> Prop) : (term449 A B C s) = (term450 A B C s).
Proof. exact (MK_COMB (@lem3622186 A B) (@lem3622185 A B C s)). Qed.
Lemma lem3622192 {A B C : Type'} : (term451 A B C) = (term452 A B C).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3622187 A B C s)). Qed.
Lemma lem3622193 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3622202 {A B C : Type'} : (term453 A B C) = (term454 A B C).
Proof. exact (MK_COMB (@lem3622193 A) (@lem3622192 A B C)). Qed.
Lemma lem3622207 {B C : Type'} (f : C -> B) (s : C -> Prop) : (term455 B C f s) = (term455 B C f s).
Proof. exact (eq_refl (term455 B C f s)). Qed.
Lemma lem3622208 {B C : Type'} (f : C -> B) : (term456 B C f) = (term456 B C f).
Proof. exact (fun_ext (fun s : C -> Prop => @lem3622207 B C f s)). Qed.
Lemma lem3622209 {C : Type'} : (@all (C -> Prop)) = (@all (C -> Prop)).
Proof. exact (eq_refl (@all (C -> Prop))). Qed.
Lemma lem3622210 {B C : Type'} (f : C -> B) : (term457 B C f) = (term457 B C f).
Proof. exact (MK_COMB (@lem3622209 C) (@lem3622208 B C f)). Qed.
Lemma lem3622211 {B C : Type'} : (term458 B C) = (term458 B C).
Proof. exact (fun_ext (fun f : C -> B => @lem3622210 B C f)). Qed.
Lemma lem3622212 {B C : Type'} : (@all (C -> B)) = (@all (C -> B)).
Proof. exact (eq_refl (@all (C -> B))). Qed.
Lemma lem3622213 {B C : Type'} : (term398 B C) = (term398 B C).
Proof. exact (MK_COMB (@lem3622212 B C) (@lem3622211 B C)). Qed.
Lemma lem3622214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3622215 {B C : Type'} : (term406 B C) = (term406 B C).
Proof. exact (MK_COMB (@lem3622214) (@lem3622213 B C)). Qed.
Lemma lem3622220 {B C : Type'} (f : B -> C) (s : B -> Prop) : (term459 B C f s) = (term459 B C f s).
Proof. exact (eq_refl (term459 B C f s)). Qed.
Lemma lem3622221 {B C : Type'} (f : B -> C) : (term460 B C f) = (term460 B C f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3622220 B C f s)). Qed.
Lemma lem3622222 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622223 {B C : Type'} (f : B -> C) : (term461 B C f) = (term461 B C f).
Proof. exact (MK_COMB (@lem3622222 B) (@lem3622221 B C f)). Qed.
Lemma lem3622224 {B C : Type'} : (term462 B C) = (term462 B C).
Proof. exact (fun_ext (fun f : B -> C => @lem3622223 B C f)). Qed.
Lemma lem3622225 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3622226 {B C : Type'} : (term399 B C) = (term399 B C).
Proof. exact (MK_COMB (@lem3622225 B C) (@lem3622224 B C)). Qed.
Lemma lem3622227 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622228 {B C : Type'} : (term407 B C) = (term407 B C).
Proof. exact (MK_COMB (@lem3622227) (@lem3622226 B C)). Qed.
Lemma lem3622229 {B C : Type'} : (term409 B C) = (term409 B C).
Proof. exact (MK_COMB (@lem3622228 B C) (@lem3622215 B C)). Qed.
Lemma lem3622234 {B : Type'} (f : B -> B) (s : B -> Prop) : (term463 B f s) = (term463 B f s).
Proof. exact (eq_refl (term463 B f s)). Qed.
Lemma lem3622235 {B : Type'} (f : B -> B) : (term464 B f) = (term464 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3622234 B f s)). Qed.
Lemma lem3622236 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622237 {B : Type'} (f : B -> B) : (term465 B f) = (term465 B f).
Proof. exact (MK_COMB (@lem3622236 B) (@lem3622235 B f)). Qed.
Lemma lem3622238 {B : Type'} : (term466 B) = (term466 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3622237 B f)). Qed.
Lemma lem3622239 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3622240 {B : Type'} : (term397 B) = (term397 B).
Proof. exact (MK_COMB (@lem3622239 B) (@lem3622238 B)). Qed.
Lemma lem3622241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622242 {B : Type'} : (term410 B) = (term410 B).
Proof. exact (MK_COMB (@lem3622241) (@lem3622240 B)). Qed.
Lemma lem3622243 {B C : Type'} : (term412 B C) = (term412 B C).
Proof. exact (MK_COMB (@lem3622242 B) (@lem3622229 B C)). Qed.
Lemma lem3622248 {A C : Type'} (f : A -> C) (s : A -> Prop) : (term459 A C f s) = (term459 A C f s).
Proof. exact (eq_refl (term459 A C f s)). Qed.
Lemma lem3622249 {A C : Type'} (f : A -> C) : (term460 A C f) = (term460 A C f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3622248 A C f s)). Qed.
Lemma lem3622250 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3622251 {A C : Type'} (f : A -> C) : (term461 A C f) = (term461 A C f).
Proof. exact (MK_COMB (@lem3622250 A) (@lem3622249 A C f)). Qed.
Lemma lem3622252 {A C : Type'} : (term462 A C) = (term462 A C).
Proof. exact (fun_ext (fun f : A -> C => @lem3622251 A C f)). Qed.
Lemma lem3622253 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem3622254 {A C : Type'} : (term399 A C) = (term399 A C).
Proof. exact (MK_COMB (@lem3622253 A C) (@lem3622252 A C)). Qed.
Lemma lem3622255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622256 {A C : Type'} : (term407 A C) = (term407 A C).
Proof. exact (MK_COMB (@lem3622255) (@lem3622254 A C)). Qed.
Lemma lem3622257 {A B C : Type'} : (term414 A B C) = (term414 A B C).
Proof. exact (MK_COMB (@lem3622256 A C) (@lem3622243 B C)). Qed.
Lemma lem3622262 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term459 A B f s) = (term459 A B f s).
Proof. exact (eq_refl (term459 A B f s)). Qed.
Lemma lem3622263 {A B : Type'} (f : A -> B) : (term460 A B f) = (term460 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3622262 A B f s)). Qed.
Lemma lem3622264 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3622265 {A B : Type'} (f : A -> B) : (term461 A B f) = (term461 A B f).
Proof. exact (MK_COMB (@lem3622264 A) (@lem3622263 A B f)). Qed.
Lemma lem3622266 {A B : Type'} : (term462 A B) = (term462 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3622265 A B f)). Qed.
Lemma lem3622267 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3622268 {A B : Type'} : (term399 A B) = (term399 A B).
Proof. exact (MK_COMB (@lem3622267 A B) (@lem3622266 A B)). Qed.
Lemma lem3622269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622270 {A B : Type'} : (term407 A B) = (term407 A B).
Proof. exact (MK_COMB (@lem3622269) (@lem3622268 A B)). Qed.
Lemma lem3622271 {A B C : Type'} : (term416 A B C) = (term416 A B C).
Proof. exact (MK_COMB (@lem3622270 A B) (@lem3622257 A B C)). Qed.
Lemma lem3622280 {C : Type'} (t : C -> Prop) (s : C -> Prop) : (term467 C t s) = (term467 C t s).
Proof. exact (eq_refl (term467 C t s)). Qed.
Lemma lem3622281 {C : Type'} (s : C -> Prop) : (term468 C s) = (term468 C s).
Proof. exact (fun_ext (fun t : C -> Prop => @lem3622280 C t s)). Qed.
Lemma lem3622282 {C : Type'} : (@all (C -> Prop)) = (@all (C -> Prop)).
Proof. exact (eq_refl (@all (C -> Prop))). Qed.
Lemma lem3622283 {C : Type'} (s : C -> Prop) : (term469 C s) = (term469 C s).
Proof. exact (MK_COMB (@lem3622282 C) (@lem3622281 C s)). Qed.
Lemma lem3622284 {C : Type'} : (term470 C) = (term470 C).
Proof. exact (fun_ext (fun s : C -> Prop => @lem3622283 C s)). Qed.
Lemma lem3622285 {C : Type'} : (@all (C -> Prop)) = (@all (C -> Prop)).
Proof. exact (eq_refl (@all (C -> Prop))). Qed.
Lemma lem3622286 {C : Type'} : (term400 C) = (term400 C).
Proof. exact (MK_COMB (@lem3622285 C) (@lem3622284 C)). Qed.
Lemma lem3622287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622288 {C : Type'} : (term417 C) = (term417 C).
Proof. exact (MK_COMB (@lem3622287) (@lem3622286 C)). Qed.
Lemma lem3622289 {A B C : Type'} : (term419 A B C) = (term419 A B C).
Proof. exact (MK_COMB (@lem3622288 C) (@lem3622271 A B C)). Qed.
Lemma lem3622298 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (term467 B t s) = (term467 B t s).
Proof. exact (eq_refl (term467 B t s)). Qed.
Lemma lem3622299 {B : Type'} (s : B -> Prop) : (term468 B s) = (term468 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3622298 B t s)). Qed.
Lemma lem3622300 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622301 {B : Type'} (s : B -> Prop) : (term469 B s) = (term469 B s).
Proof. exact (MK_COMB (@lem3622300 B) (@lem3622299 B s)). Qed.
Lemma lem3622302 {B : Type'} : (term470 B) = (term470 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3622301 B s)). Qed.
Lemma lem3622303 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622304 {B : Type'} : (term400 B) = (term400 B).
Proof. exact (MK_COMB (@lem3622303 B) (@lem3622302 B)). Qed.
Lemma lem3622305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622306 {B : Type'} : (term417 B) = (term417 B).
Proof. exact (MK_COMB (@lem3622305) (@lem3622304 B)). Qed.
Lemma lem3622307 {A B C : Type'} : (term421 A B C) = (term421 A B C).
Proof. exact (MK_COMB (@lem3622306 B) (@lem3622289 A B C)). Qed.
Lemma lem3622316 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term467 A t s) = (term467 A t s).
Proof. exact (eq_refl (term467 A t s)). Qed.
Lemma lem3622317 {A : Type'} (s : A -> Prop) : (term468 A s) = (term468 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3622316 A t s)). Qed.
Lemma lem3622318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3622319 {A : Type'} (s : A -> Prop) : (term469 A s) = (term469 A s).
Proof. exact (MK_COMB (@lem3622318 A) (@lem3622317 A s)). Qed.
Lemma lem3622320 {A : Type'} : (term470 A) = (term470 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3622319 A s)). Qed.
Lemma lem3622321 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3622322 {A : Type'} : (term400 A) = (term400 A).
Proof. exact (MK_COMB (@lem3622321 A) (@lem3622320 A)). Qed.
Lemma lem3622323 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622324 {A : Type'} : (term417 A) = (term417 A).
Proof. exact (MK_COMB (@lem3622323) (@lem3622322 A)). Qed.
Lemma lem3622325 {A B C : Type'} : (term423 A B C) = (term423 A B C).
Proof. exact (MK_COMB (@lem3622324 A) (@lem3622307 A B C)). Qed.
Lemma lem3622330 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term424 A B C h f s) = (term424 A B C h f s).
Proof. exact (eq_refl (term424 A B C h f s)). Qed.
Lemma lem3622331 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term426 A B C h f s) = (term426 A B C h f s).
Proof. exact (MK_COMB (@lem3622330 A B C h f s) (@lem3622325 A B C)). Qed.
Lemma lem3622336 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (x : A) : (term46 A B C s g h f x) = (term46 A B C s g h f x).
Proof. exact (eq_refl (term46 A B C s g h f x)). Qed.
Lemma lem3622337 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term48 A B C s g h f) = (term48 A B C s g h f).
Proof. exact (fun_ext (fun x : A => @lem3622336 A B C s g h f x)). Qed.
Lemma lem3622338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3622339 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term50 A B C s g h f) = (term50 A B C s g h f).
Proof. exact (MK_COMB (@lem3622338 A) (@lem3622337 A B C s g h f)). Qed.
Lemma lem3622340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3622341 {A B C : Type'} (s : A -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) : (term427 A B C s g h f) = (term427 A B C s g h f).
Proof. exact (MK_COMB (@lem3622340) (@lem3622339 A B C s g h f)). Qed.
Lemma lem3622342 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term429 A B C g h f s) = (term429 A B C g h f s).
Proof. exact (MK_COMB (@lem3622341 A B C s g h f) (@lem3622331 A B C h f s)). Qed.
Lemma lem3622345 {B : Type'} (t : B -> Prop) : (term430 B t) = (term430 B t).
Proof. exact (eq_refl (term430 B t)). Qed.
Lemma lem3622346 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term432 A B C t g h f s) = (term432 A B C t g h f s).
Proof. exact (MK_COMB (@lem3622345 B t) (@lem3622342 A B C g h f s)). Qed.
Lemma lem3622349 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term433 A B f s t) = (term433 A B f s t).
Proof. exact (eq_refl (term433 A B f s t)). Qed.
Lemma lem3622350 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term434 A B C t g h f s) = (term434 A B C t g h f s).
Proof. exact (MK_COMB (@lem3622349 A B f s t) (@lem3622346 A B C t g h f s)). Qed.
Lemma lem3622351 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term436 A B C g h f s) = (term436 A B C g h f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3622350 A B C t g h f s)). Qed.
Lemma lem3622352 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622353 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term438 A B C g h f s) = (term438 A B C g h f s).
Proof. exact (MK_COMB (@lem3622352 B) (@lem3622351 A B C g h f s)). Qed.
Lemma lem3622354 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term440 A B C h f s) = (term440 A B C h f s).
Proof. exact (fun_ext (fun g : A -> C => @lem3622353 A B C g h f s)). Qed.
Lemma lem3622355 {A C : Type'} : (@all (A -> C)) = (@all (A -> C)).
Proof. exact (eq_refl (@all (A -> C))). Qed.
Lemma lem3622356 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term442 A B C h f s) = (term442 A B C h f s).
Proof. exact (MK_COMB (@lem3622355 A C) (@lem3622354 A B C h f s)). Qed.
Lemma lem3622357 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term444 A B C f s) = (term444 A B C f s).
Proof. exact (fun_ext (fun h : B -> C => @lem3622356 A B C h f s)). Qed.
Lemma lem3622358 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3622359 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term446 A B C f s) = (term446 A B C f s).
Proof. exact (MK_COMB (@lem3622358 B C) (@lem3622357 A B C f s)). Qed.
Lemma lem3622360 {A B C : Type'} (s : A -> Prop) : (term448 A B C s) = (term448 A B C s).
Proof. exact (fun_ext (fun f : A -> B => @lem3622359 A B C f s)). Qed.
Lemma lem3622361 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3622362 {A B C : Type'} (s : A -> Prop) : (term450 A B C s) = (term450 A B C s).
Proof. exact (MK_COMB (@lem3622361 A B) (@lem3622360 A B C s)). Qed.
Lemma lem3622363 {A B C : Type'} : (term452 A B C) = (term452 A B C).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3622362 A B C s)). Qed.
Lemma lem3622364 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3622365 {A B C : Type'} : (term454 A B C) = (term454 A B C).
Proof. exact (MK_COMB (@lem3622364 A) (@lem3622363 A B C)). Qed.
Lemma lem3622546 {A B C : Type'} : (term453 A B C) = (term454 A B C).
Proof. exact (TRANS (@lem3622202 A B C) (@lem3622365 A B C)). Qed.
Lemma lem3622547 {A B C : Type'} : (term454 A B C) = (term453 A B C).
Proof. exact (SYM (@lem3622546 A B C)). Qed.
Lemma lem3622553 {B : Type'} (h1 : term400 B) : term400 B.
Proof. exact (h1). Qed.
Lemma lem3622558 {B C : Type'} (h1 : term399 B C) : term399 B C.
Proof. exact (h1). Qed.
Lemma lem3622565 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term16 A B f s t.
Proof. exact (h1). Qed.
Lemma lem3622571 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem3622640 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term396 A B C h f s) : term396 A B C h f s.
Proof. exact (h1). Qed.
Lemma lem3622801 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term471 B s t) = (term472 B s t).
Proof. exact (@lem17045 (@FINITE B t) (@SUBSET B s t)). Qed.
Lemma lem3622802 {B : Type'} (s : B -> Prop) : (@FINITE B s) = (@FINITE B s).
Proof. exact (eq_refl (@FINITE B s)). Qed.
Lemma lem3622803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3622804 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term473 B s t) = (term474 B s t).
Proof. exact (MK_COMB (@lem3622803) (@lem3622801 B s t)). Qed.
Lemma lem3622805 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (term475 B t s) = (term476 B t s).
Proof. exact (MK_COMB (@lem3622804 B s t) (@lem3622802 B s)). Qed.
Lemma lem3622806 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (term467 B t s) = (term475 B t s).
Proof. exact (@lem17265 (term477 B s t) (@FINITE B s)). Qed.
Lemma lem3622807 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (term467 B t s) = (term476 B t s).
Proof. exact (TRANS (@lem3622806 B t s) (@lem3622805 B t s)). Qed.
Lemma lem3622808 {B : Type'} (s : B -> Prop) : (term468 B s) = (term478 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3622807 B t s)). Qed.
Lemma lem3622809 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622810 {B : Type'} (s : B -> Prop) : (term469 B s) = (term479 B s).
Proof. exact (MK_COMB (@lem3622809 B) (@lem3622808 B s)). Qed.
Lemma lem3622811 {B : Type'} : (term470 B) = (term480 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3622810 B s)). Qed.
Lemma lem3622812 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622813 {B : Type'} : (term400 B) = (term481 B).
Proof. exact (MK_COMB (@lem3622812 B) (@lem3622811 B)). Qed.
Lemma lem3622839 {A : Type'} (P : A -> Prop) (Q : Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3622840 {B : Type'} (P : type686 B) (Q : Prop) : (term484 B P Q) = (term485 B P Q).
Proof. exact (@lem3622839 (B -> Prop) P Q). Qed.
Lemma lem3622841 {B : Type'} (s : B -> Prop) : (term486 B s) = (term487 B s).
Proof. exact (@lem3622840 B (term488 B s) (@FINITE B s)). Qed.
Lemma lem3622842 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term489 B s t) = (term472 B s t).
Proof. exact (eq_refl (term489 B s t)). Qed.
Lemma lem3622843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3622844 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term490 B s t) = (term474 B s t).
Proof. exact (MK_COMB (@lem3622843) (@lem3622842 B s t)). Qed.
Lemma lem3622845 {B : Type'} (s : B -> Prop) : (@FINITE B s) = (@FINITE B s).
Proof. exact (eq_refl (@FINITE B s)). Qed.
Lemma lem3622846 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (term491 B t s) = (term476 B t s).
Proof. exact (MK_COMB (@lem3622844 B s t) (@lem3622845 B s)). Qed.
Lemma lem3622847 {B : Type'} (s : B -> Prop) : (term492 B s) = (term478 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3622846 B t s)). Qed.
Lemma lem3622848 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622849 {B : Type'} (s : B -> Prop) : (term486 B s) = (term479 B s).
Proof. exact (MK_COMB (@lem3622848 B) (@lem3622847 B s)). Qed.
Lemma lem3622850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3622851 {B : Type'} (s : B -> Prop) : (term493 B s) = (term494 B s).
Proof. exact (MK_COMB (@lem3622850) (@lem3622849 B s)). Qed.
Lemma lem3622852 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term489 B s t) = (term472 B s t).
Proof. exact (eq_refl (term489 B s t)). Qed.
Lemma lem3622853 {B : Type'} (s : B -> Prop) : (term495 B s) = (term488 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3622852 B s t)). Qed.
Lemma lem3622854 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622855 {B : Type'} (s : B -> Prop) : (term496 B s) = (term497 B s).
Proof. exact (MK_COMB (@lem3622854 B) (@lem3622853 B s)). Qed.
Lemma lem3622856 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3622857 {B : Type'} (s : B -> Prop) : (term498 B s) = (term499 B s).
Proof. exact (MK_COMB (@lem3622856) (@lem3622855 B s)). Qed.
Lemma lem3622858 {B : Type'} (s : B -> Prop) : (@FINITE B s) = (@FINITE B s).
Proof. exact (eq_refl (@FINITE B s)). Qed.
Lemma lem3622859 {B : Type'} (s : B -> Prop) : (term487 B s) = (term500 B s).
Proof. exact (MK_COMB (@lem3622857 B s) (@lem3622858 B s)). Qed.
Lemma lem3622860 {B : Type'} (s : B -> Prop) : ((term486 B s) = (term487 B s)) = ((term479 B s) = (term500 B s)).
Proof. exact (MK_COMB (@lem3622851 B s) (@lem3622859 B s)). Qed.
Lemma lem3622861 {B : Type'} (s : B -> Prop) : (term479 B s) = (term500 B s).
Proof. exact (EQ_MP (@lem3622860 B s) (@lem3622841 B s)). Qed.
Lemma lem3622910 {B : Type'} : (term480 B) = (term501 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3622861 B s)). Qed.
Lemma lem3622911 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3622946 {B : Type'} : (term481 B) = (term502 B).
Proof. exact (MK_COMB (@lem3622911 B) (@lem3622910 B)). Qed.
Lemma lem3622947 {B : Type'} : (term400 B) = (term502 B).
Proof. exact (TRANS (@lem3622813 B) (@lem3622946 B)). Qed.
Lemma lem3622948 {B : Type'} (h1 : term400 B) : term502 B.
Proof. exact (EQ_MP (@lem3622947 B) (@lem3622553 B h1)). Qed.
Lemma lem3623319 {B C : Type'} (f : B -> C) (s : B -> Prop) : (term459 B C f s) = (term503 B C f s).
Proof. exact (@lem17265 (@FINITE B s) (term60 B C f s)). Qed.
Lemma lem3623320 {B C : Type'} (f : B -> C) : (term460 B C f) = (term504 B C f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3623319 B C f s)). Qed.
Lemma lem3623321 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623322 {B C : Type'} (f : B -> C) : (term461 B C f) = (term505 B C f).
Proof. exact (MK_COMB (@lem3623321 B) (@lem3623320 B C f)). Qed.
Lemma lem3623323 {B C : Type'} : (term462 B C) = (term506 B C).
Proof. exact (fun_ext (fun f : B -> C => @lem3623322 B C f)). Qed.
Lemma lem3623324 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3623381 {B C : Type'} : (term399 B C) = (term507 B C).
Proof. exact (MK_COMB (@lem3623324 B C) (@lem3623323 B C)). Qed.
Lemma lem3623382 {B C : Type'} (h1 : term399 B C) : term507 B C.
Proof. exact (EQ_MP (@lem3623381 B C) (@lem3622558 B C h1)). Qed.
Lemma lem3623462 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term16 A B f s t.
Proof. exact (h1). Qed.
Lemma lem3623466 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem3623514 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term396 A B C h f s) : term396 A B C h f s.
Proof. exact (h1). Qed.
Lemma lem3623545 {B : Type'} (s : B -> Prop) : (@FINITE B s) = (@FINITE B s).
Proof. exact (eq_refl (@FINITE B s)). Qed.
Lemma lem3623560 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term472 B s t) = (term472 B s t).
Proof. exact (eq_refl (term472 B s t)). Qed.
Lemma lem3623561 {B : Type'} (s : B -> Prop) : (term488 B s) = (term488 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3623560 B s t)). Qed.
Lemma lem3623562 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623563 {B : Type'} (s : B -> Prop) : (term497 B s) = (term497 B s).
Proof. exact (MK_COMB (@lem3623562 B) (@lem3623561 B s)). Qed.
Lemma lem3623564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3623565 {B : Type'} (s : B -> Prop) : (term499 B s) = (term499 B s).
Proof. exact (MK_COMB (@lem3623564) (@lem3623563 B s)). Qed.
Lemma lem3623566 {B : Type'} (s : B -> Prop) : (term500 B s) = (term500 B s).
Proof. exact (MK_COMB (@lem3623565 B s) (@lem3623545 B s)). Qed.
Lemma lem3623567 {B : Type'} : (term501 B) = (term501 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3623566 B s)). Qed.
Lemma lem3623568 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623569 {B : Type'} : (term502 B) = (term502 B).
Proof. exact (MK_COMB (@lem3623568 B) (@lem3623567 B)). Qed.
Lemma lem3623570 {B : Type'} (h1 : term400 B) : term502 B.
Proof. exact (EQ_MP (@lem3623569 B) (@lem3622948 B h1)). Qed.
Lemma lem3623679 {B C : Type'} (f : B -> C) (s : B -> Prop) : (term503 B C f s) = (term503 B C f s).
Proof. exact (eq_refl (term503 B C f s)). Qed.
Lemma lem3623680 {B C : Type'} (f : B -> C) : (term504 B C f) = (term504 B C f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3623679 B C f s)). Qed.
Lemma lem3623681 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623682 {B C : Type'} (f : B -> C) : (term505 B C f) = (term505 B C f).
Proof. exact (MK_COMB (@lem3623681 B) (@lem3623680 B C f)). Qed.
Lemma lem3623683 {B C : Type'} : (term506 B C) = (term506 B C).
Proof. exact (fun_ext (fun f : B -> C => @lem3623682 B C f)). Qed.
Lemma lem3623684 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3623685 {B C : Type'} : (term507 B C) = (term507 B C).
Proof. exact (MK_COMB (@lem3623684 B C) (@lem3623683 B C)). Qed.
Lemma lem3623686 {B C : Type'} (h1 : term399 B C) : term507 B C.
Proof. exact (EQ_MP (@lem3623685 B C) (@lem3623382 B C h1)). Qed.
Lemma lem3623712 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term16 A B f s t.
Proof. exact (h1). Qed.
Lemma lem3623716 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem3623733 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term396 A B C h f s) : term396 A B C h f s.
Proof. exact (h1). Qed.
Lemma lem3623783 {A : Type'} (P : A -> Prop) (Q : Prop) : (term483 A P Q) = (term482 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3623784 {B : Type'} (P : type686 B) (Q : Prop) : (term485 B P Q) = (term484 B P Q).
Proof. exact (@lem3623783 (B -> Prop) P Q). Qed.
Lemma lem3623785 {B : Type'} (s : B -> Prop) : (term487 B s) = (term486 B s).
Proof. exact (@lem3623784 B (term488 B s) (@FINITE B s)). Qed.
Lemma lem3623786 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term489 B s t) = (term472 B s t).
Proof. exact (eq_refl (term489 B s t)). Qed.
Lemma lem3623787 {B : Type'} (s : B -> Prop) : (term495 B s) = (term488 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3623786 B s t)). Qed.
Lemma lem3623788 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623789 {B : Type'} (s : B -> Prop) : (term496 B s) = (term497 B s).
Proof. exact (MK_COMB (@lem3623788 B) (@lem3623787 B s)). Qed.
Lemma lem3623790 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3623791 {B : Type'} (s : B -> Prop) : (term498 B s) = (term499 B s).
Proof. exact (MK_COMB (@lem3623790) (@lem3623789 B s)). Qed.
Lemma lem3623792 {B : Type'} (s : B -> Prop) : (@FINITE B s) = (@FINITE B s).
Proof. exact (eq_refl (@FINITE B s)). Qed.
Lemma lem3623793 {B : Type'} (s : B -> Prop) : (term487 B s) = (term500 B s).
Proof. exact (MK_COMB (@lem3623791 B s) (@lem3623792 B s)). Qed.
Lemma lem3623794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3623795 {B : Type'} (s : B -> Prop) : (term508 B s) = (term509 B s).
Proof. exact (MK_COMB (@lem3623794) (@lem3623793 B s)). Qed.
Lemma lem3623796 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term489 B s t) = (term472 B s t).
Proof. exact (eq_refl (term489 B s t)). Qed.
Lemma lem3623797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3623798 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (term490 B s t) = (term474 B s t).
Proof. exact (MK_COMB (@lem3623797) (@lem3623796 B s t)). Qed.
Lemma lem3623799 {B : Type'} (s : B -> Prop) : (@FINITE B s) = (@FINITE B s).
Proof. exact (eq_refl (@FINITE B s)). Qed.
Lemma lem3623800 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (term491 B t s) = (term476 B t s).
Proof. exact (MK_COMB (@lem3623798 B s t) (@lem3623799 B s)). Qed.
Lemma lem3623801 {B : Type'} (s : B -> Prop) : (term492 B s) = (term478 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3623800 B t s)). Qed.
Lemma lem3623802 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623803 {B : Type'} (s : B -> Prop) : (term486 B s) = (term479 B s).
Proof. exact (MK_COMB (@lem3623802 B) (@lem3623801 B s)). Qed.
Lemma lem3623804 {B : Type'} (s : B -> Prop) : ((term487 B s) = (term486 B s)) = ((term500 B s) = (term479 B s)).
Proof. exact (MK_COMB (@lem3623795 B s) (@lem3623803 B s)). Qed.
Lemma lem3623805 {B : Type'} (s : B -> Prop) : (term500 B s) = (term479 B s).
Proof. exact (EQ_MP (@lem3623804 B s) (@lem3623785 B s)). Qed.
Lemma lem3623806 {B : Type'} : (term501 B) = (term480 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3623805 B s)). Qed.
Lemma lem3623807 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623808 {B : Type'} : (term502 B) = (term481 B).
Proof. exact (MK_COMB (@lem3623807 B) (@lem3623806 B)). Qed.
Lemma lem3623821 {B : Type'} (t : B -> Prop) (s : B -> Prop) : (term476 B t s) = (term476 B t s).
Proof. exact (eq_refl (term476 B t s)). Qed.
Lemma lem3623822 {B : Type'} (s : B -> Prop) : (term478 B s) = (term478 B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3623821 B t s)). Qed.
Lemma lem3623823 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623824 {B : Type'} (s : B -> Prop) : (term479 B s) = (term479 B s).
Proof. exact (MK_COMB (@lem3623823 B) (@lem3623822 B s)). Qed.
Lemma lem3623825 {B : Type'} : (term480 B) = (term480 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3623824 B s)). Qed.
Lemma lem3623826 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623827 {B : Type'} : (term481 B) = (term481 B).
Proof. exact (MK_COMB (@lem3623826 B) (@lem3623825 B)). Qed.
Lemma lem3623828 {B : Type'} : (term502 B) = (term481 B).
Proof. exact (TRANS (@lem3623808 B) (@lem3623827 B)). Qed.
Lemma lem3623829 {B : Type'} (h1 : term400 B) : term481 B.
Proof. exact (EQ_MP (@lem3623828 B) (@lem3623570 B h1)). Qed.
Lemma lem3623933 {B C : Type'} (f : B -> C) (s : B -> Prop) : (term503 B C f s) = (term503 B C f s).
Proof. exact (eq_refl (term503 B C f s)). Qed.
Lemma lem3623934 {B C : Type'} (f : B -> C) : (term504 B C f) = (term504 B C f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3623933 B C f s)). Qed.
Lemma lem3623935 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3623936 {B C : Type'} (f : B -> C) : (term505 B C f) = (term505 B C f).
Proof. exact (MK_COMB (@lem3623935 B) (@lem3623934 B C f)). Qed.
Lemma lem3623937 {B C : Type'} : (term506 B C) = (term506 B C).
Proof. exact (fun_ext (fun f : B -> C => @lem3623936 B C f)). Qed.
Lemma lem3623938 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem3623940 {B C : Type'} : (term507 B C) = (term507 B C).
Proof. exact (MK_COMB (@lem3623938 B C) (@lem3623937 B C)). Qed.
Lemma lem3623941 {B C : Type'} (h1 : term399 B C) : term507 B C.
Proof. exact (EQ_MP (@lem3623940 B C) (@lem3623686 B C h1)). Qed.
Lemma lem3623967 {B : Type'} (_39404 : B -> Prop) (h1 : term400 B) : term510 B _39404.
Proof. exact (@lem3623829 B h1 _39404). Qed.
Lemma lem3623968 {B : Type'} (_39404 : B -> Prop) : (term510 B _39404) = (term479 B _39404).
Proof. exact (eq_refl (term510 B _39404)). Qed.
Lemma lem3623969 {B : Type'} (_39404 : B -> Prop) (h1 : term400 B) : term479 B _39404.
Proof. exact (EQ_MP (@lem3623968 B _39404) (@lem3623967 B _39404 h1)). Qed.
Lemma lem3623970 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) (h1 : term400 B) : term511 B _39404 _39405.
Proof. exact (@lem3623969 B _39404 h1 _39405). Qed.
Lemma lem3623971 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) : (term511 B _39404 _39405) = (term476 B _39405 _39404).
Proof. exact (eq_refl (term511 B _39404 _39405)). Qed.
Lemma lem3623972 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) (h1 : term400 B) : term476 B _39405 _39404.
Proof. exact (EQ_MP (@lem3623971 B _39405 _39404) (@lem3623970 B _39404 _39405 h1)). Qed.
Lemma lem3623997 {B C : Type'} (_39414 : B -> C) (h1 : term399 B C) : term512 B C _39414.
Proof. exact (@lem3623941 B C h1 _39414). Qed.
Lemma lem3623998 {B C : Type'} (_39414 : B -> C) : (term512 B C _39414) = (term505 B C _39414).
Proof. exact (eq_refl (term512 B C _39414)). Qed.
Lemma lem3623999 {B C : Type'} (_39414 : B -> C) (h1 : term399 B C) : term505 B C _39414.
Proof. exact (EQ_MP (@lem3623998 B C _39414) (@lem3623997 B C _39414 h1)). Qed.
Lemma lem3624000 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) (h1 : term399 B C) : term513 B C _39414 _39415.
Proof. exact (@lem3623999 B C _39414 h1 _39415). Qed.
Lemma lem3624001 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term513 B C _39414 _39415) = (term503 B C _39414 _39415).
Proof. exact (eq_refl (term513 B C _39414 _39415)). Qed.
Lemma lem3624010 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term16 A B f s t.
Proof. exact (h1). Qed.
Lemma lem3624012 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem3624020 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term396 A B C h f s) : term396 A B C h f s.
Proof. exact (h1). Qed.
Lemma lem3624043 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) : (term476 B _39405 _39404) = (term514 B _39405 _39404).
Proof. exact (@lem3619189 (term515 B _39405) (term516 B _39404 _39405) (@FINITE B _39404)). Qed.
Lemma lem3624044 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) (h1 : term400 B) : term514 B _39405 _39404.
Proof. exact (EQ_MP (@lem3624043 B _39405 _39404) (@lem3623972 B _39405 _39404 h1)). Qed.
Lemma lem3624080 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) (h1 : term399 B C) : term503 B C _39414 _39415.
Proof. exact (EQ_MP (@lem3624001 B C _39414 _39415) (@lem3624000 B C _39414 _39415 h1)). Qed.
Lemma lem3624335 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem3624336 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : term517 B t.
Proof. exact (fun h0 : term515 B t => @lem3624335 B t h1). Qed.
Lemma lem3624338 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3624339 {B : Type'} (t : B -> Prop) : (term517 B t) = (@FINITE B t).
Proof. exact (@lem3624338 (@FINITE B t)). Qed.
Lemma lem3624340 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem3624339 B t) (@lem3624336 B t h1)). Qed.
Lemma lem3624342 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term16 A B f s t.
Proof. exact (h1). Qed.
Lemma lem3624343 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term518 A B f s t.
Proof. exact (fun h0 : term519 A B f s t => @lem3624342 A B f s t h1). Qed.
Lemma lem3624345 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3624346 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term518 A B f s t) = (term16 A B f s t).
Proof. exact (@lem3624345 (term16 A B f s t)). Qed.
Lemma lem3624347 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term16 A B f s t.
Proof. exact (EQ_MP (@lem3624346 A B f s t) (@lem3624343 A B f s t h1)). Qed.
Lemma lem3624363 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3624364 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term520 B _39405 _39404) = (term521 B _39404 _39405).
Proof. exact (@lem3624363 (@FINITE B _39404) (term516 B _39404 _39405)). Qed.
Lemma lem3624370 {B : Type'} (_39405 : B -> Prop) : (term522 B _39405) = (term522 B _39405).
Proof. exact (eq_refl (term522 B _39405)). Qed.
Lemma lem3624371 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term514 B _39405 _39404) = (term523 B _39404 _39405).
Proof. exact (MK_COMB (@lem3624370 B _39405) (@lem3624364 B _39404 _39405)). Qed.
Lemma lem3624375 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3624376 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term523 B _39404 _39405) = (term524 B _39404 _39405).
Proof. exact (@lem3624375 (@FINITE B _39404) (term515 B _39405) (term516 B _39404 _39405)). Qed.
Lemma lem3624392 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term514 B _39405 _39404) = (term524 B _39404 _39405).
Proof. exact (TRANS (@lem3624371 B _39404 _39405) (@lem3624376 B _39404 _39405)). Qed.
Lemma lem3624393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3624394 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term525 B _39405 _39404) = (term526 B _39404 _39405).
Proof. exact (MK_COMB (@lem3624393) (@lem3624392 B _39404 _39405)). Qed.
Lemma lem3624410 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term524 B _39404 _39405) = (term524 B _39404 _39405).
Proof. exact (eq_refl (term524 B _39404 _39405)). Qed.
Lemma lem3624411 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : ((term514 B _39405 _39404) = (term524 B _39404 _39405)) = ((term524 B _39404 _39405) = (term524 B _39404 _39405)).
Proof. exact (MK_COMB (@lem3624394 B _39404 _39405) (@lem3624410 B _39404 _39405)). Qed.
Lemma lem3624413 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3624414 (x : Prop) : (x = x) = True.
Proof. exact (@lem3624413 Prop x). Qed.
Lemma lem3624415 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : ((term524 B _39404 _39405) = (term524 B _39404 _39405)) = True.
Proof. exact (@lem3624414 (term524 B _39404 _39405)). Qed.
Lemma lem3624416 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : ((term514 B _39405 _39404) = (term524 B _39404 _39405)) = True.
Proof. exact (TRANS (@lem3624411 B _39404 _39405) (@lem3624415 B _39404 _39405)). Qed.
Lemma lem3624417 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : True = ((term514 B _39405 _39404) = (term524 B _39404 _39405)).
Proof. exact (SYM (@lem3624416 B _39404 _39405)). Qed.
Lemma lem3624418 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term514 B _39405 _39404) = (term524 B _39404 _39405).
Proof. exact (EQ_MP (@lem3624417 B _39404 _39405) (@lem0)). Qed.
Lemma lem3624419 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) (h1 : term400 B) : term524 B _39404 _39405.
Proof. exact (EQ_MP (@lem3624418 B _39404 _39405) (@lem3624044 B _39405 _39404 h1)). Qed.
Lemma lem3624421 (b : Prop) (a : Prop) : (a \/ b) = (term340 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3624422 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) : (term524 B _39404 _39405) = (term527 B _39405 _39404).
Proof. exact (@lem3624421 (term472 B _39404 _39405) (@FINITE B _39404)). Qed.
Lemma lem3624424 (a : Prop) (b : Prop) : (term370 a b) = (term371 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3624425 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term528 B _39404 _39405) = (term529 B _39404 _39405).
Proof. exact (@lem3624424 (term515 B _39405) (term516 B _39404 _39405)). Qed.
Lemma lem3624427 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3624428 {B : Type'} (_39405 : B -> Prop) : (term530 B _39405) = (@FINITE B _39405).
Proof. exact (@lem3624427 (@FINITE B _39405)). Qed.
Lemma lem3624429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3624430 {B : Type'} (_39405 : B -> Prop) : (term531 B _39405) = (term66 B _39405).
Proof. exact (MK_COMB (@lem3624429) (@lem3624428 B _39405)). Qed.
Lemma lem3624432 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3624433 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term532 B _39404 _39405) = (@SUBSET B _39404 _39405).
Proof. exact (@lem3624432 (@SUBSET B _39404 _39405)). Qed.
Lemma lem3624434 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term529 B _39404 _39405) = (term477 B _39404 _39405).
Proof. exact (MK_COMB (@lem3624430 B _39405) (@lem3624433 B _39404 _39405)). Qed.
Lemma lem3624435 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term528 B _39404 _39405) = (term477 B _39404 _39405).
Proof. exact (TRANS (@lem3624425 B _39404 _39405) (@lem3624434 B _39404 _39405)). Qed.
Lemma lem3624436 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3624437 {B : Type'} (_39404 : B -> Prop) (_39405 : B -> Prop) : (term533 B _39404 _39405) = (term534 B _39404 _39405).
Proof. exact (MK_COMB (@lem3624436) (@lem3624435 B _39404 _39405)). Qed.
Lemma lem3624438 {B : Type'} (_39404 : B -> Prop) : (@FINITE B _39404) = (@FINITE B _39404).
Proof. exact (eq_refl (@FINITE B _39404)). Qed.
Lemma lem3624439 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) : (term527 B _39405 _39404) = (term467 B _39405 _39404).
Proof. exact (MK_COMB (@lem3624437 B _39404 _39405) (@lem3624438 B _39404)). Qed.
Lemma lem3624440 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) : (term524 B _39404 _39405) = (term467 B _39405 _39404).
Proof. exact (TRANS (@lem3624422 B _39405 _39404) (@lem3624439 B _39405 _39404)). Qed.
Lemma lem3624442 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term16 A B f s t) : term62 A B f s t.
Proof. exact (conj (@lem3624340 B t h1) (@lem3624347 A B f s t h2)). Qed.
Lemma lem3624444 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) (h1 : term400 B) : term467 B _39405 _39404.
Proof. exact (EQ_MP (@lem3624440 B _39405 _39404) (@lem3624419 B _39404 _39405 h1)). Qed.
Lemma lem3624445 {B : Type'} (_39405 : B -> Prop) (_39404 : B -> Prop) (h1 : term400 B) : term467 B _39405 _39404.
Proof. exact (@lem3624444 B _39405 _39404 h1). Qed.
Lemma lem3624446 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) (h1 : term400 B) : term535 A B t f s.
Proof. exact (@lem3624445 B t (@IMAGE A B f s) h1). Qed.
Lemma lem3624449 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term60 A B f s.
Proof. exact (@lem3624446 A B t f s h1 (@lem3624442 A B f s t h2 h3)). Qed.
Lemma lem3624450 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term536 A B f s.
Proof. exact (fun h0 : term537 A B f s => @lem3624449 A B f s t h1 h2 h3). Qed.
Lemma lem3624452 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3624453 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term536 A B f s) = (term60 A B f s).
Proof. exact (@lem3624452 (term60 A B f s)). Qed.
Lemma lem3624454 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term60 A B f s.
Proof. exact (EQ_MP (@lem3624453 A B f s) (@lem3624450 A B f s t h1 h2 h3)). Qed.
Lemma lem3624460 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3624461 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term503 B C _39414 _39415) = (term538 B C _39414 _39415).
Proof. exact (@lem3624460 (term60 B C _39414 _39415) (term515 B _39415)). Qed.
Lemma lem3624467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3624468 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term539 B C _39414 _39415) = (term540 B C _39414 _39415).
Proof. exact (MK_COMB (@lem3624467) (@lem3624461 B C _39414 _39415)). Qed.
Lemma lem3624474 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term538 B C _39414 _39415) = (term538 B C _39414 _39415).
Proof. exact (eq_refl (term538 B C _39414 _39415)). Qed.
Lemma lem3624475 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : ((term503 B C _39414 _39415) = (term538 B C _39414 _39415)) = ((term538 B C _39414 _39415) = (term538 B C _39414 _39415)).
Proof. exact (MK_COMB (@lem3624468 B C _39414 _39415) (@lem3624474 B C _39414 _39415)). Qed.
Lemma lem3624477 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3624478 (x : Prop) : (x = x) = True.
Proof. exact (@lem3624477 Prop x). Qed.
Lemma lem3624479 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : ((term538 B C _39414 _39415) = (term538 B C _39414 _39415)) = True.
Proof. exact (@lem3624478 (term538 B C _39414 _39415)). Qed.
Lemma lem3624480 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : ((term503 B C _39414 _39415) = (term538 B C _39414 _39415)) = True.
Proof. exact (TRANS (@lem3624475 B C _39414 _39415) (@lem3624479 B C _39414 _39415)). Qed.
Lemma lem3624481 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : True = ((term503 B C _39414 _39415) = (term538 B C _39414 _39415)).
Proof. exact (SYM (@lem3624480 B C _39414 _39415)). Qed.
Lemma lem3624482 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term503 B C _39414 _39415) = (term538 B C _39414 _39415).
Proof. exact (EQ_MP (@lem3624481 B C _39414 _39415) (@lem0)). Qed.
Lemma lem3624483 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) (h1 : term399 B C) : term538 B C _39414 _39415.
Proof. exact (EQ_MP (@lem3624482 B C _39414 _39415) (@lem3624080 B C _39414 _39415 h1)). Qed.
Lemma lem3624485 (b : Prop) (a : Prop) : (a \/ b) = (term340 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3624486 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term538 B C _39414 _39415) = (term541 B C _39414 _39415).
Proof. exact (@lem3624485 (term515 B _39415) (term60 B C _39414 _39415)). Qed.
Lemma lem3624488 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3624489 {B : Type'} (_39415 : B -> Prop) : (term530 B _39415) = (@FINITE B _39415).
Proof. exact (@lem3624488 (@FINITE B _39415)). Qed.
Lemma lem3624490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3624491 {B : Type'} (_39415 : B -> Prop) : (term542 B _39415) = (term430 B _39415).
Proof. exact (MK_COMB (@lem3624490) (@lem3624489 B _39415)). Qed.
Lemma lem3624492 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term60 B C _39414 _39415) = (term60 B C _39414 _39415).
Proof. exact (eq_refl (term60 B C _39414 _39415)). Qed.
Lemma lem3624493 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term541 B C _39414 _39415) = (term459 B C _39414 _39415).
Proof. exact (MK_COMB (@lem3624491 B _39415) (@lem3624492 B C _39414 _39415)). Qed.
Lemma lem3624494 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) : (term538 B C _39414 _39415) = (term459 B C _39414 _39415).
Proof. exact (TRANS (@lem3624486 B C _39414 _39415) (@lem3624493 B C _39414 _39415)). Qed.
Lemma lem3624497 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) (h1 : term399 B C) : term459 B C _39414 _39415.
Proof. exact (EQ_MP (@lem3624494 B C _39414 _39415) (@lem3624483 B C _39414 _39415 h1)). Qed.
Lemma lem3624498 {B C : Type'} (_39414 : B -> C) (_39415 : B -> Prop) (h1 : term399 B C) : term459 B C _39414 _39415.
Proof. exact (@lem3624497 B C _39414 _39415 h1). Qed.
Lemma lem3624499 {A B C : Type'} (_39414 : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term399 B C) : term543 A B C _39414 f s.
Proof. exact (@lem3624498 B C _39414 (@IMAGE A B f s) h1). Qed.
Lemma lem3624502 {A B C : Type'} (_39414 : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term16 A B f s t) : term58 A B C _39414 f s.
Proof. exact (@lem3624499 A B C _39414 f s h1 (@lem3624454 A B f s t h2 h3 h4)). Qed.
Lemma lem3624503 {A B C : Type'} (_39414 : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term16 A B f s t) : term58 A B C _39414 f s.
Proof. exact (@lem3624502 A B C _39414 f s t h1 h2 h3 h4). Qed.
Lemma lem3624504 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term16 A B f s t) : term58 A B C h f s.
Proof. exact (@lem3624503 A B C h f s t h1 h2 h3 h4). Qed.
Lemma lem3624505 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term16 A B f s t) : term544 A B C h f s.
Proof. exact (fun h0 : term396 A B C h f s => @lem3624504 A B C h f s t h1 h2 h3 h4). Qed.
Lemma lem3624507 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3624508 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term544 A B C h f s) = (term58 A B C h f s).
Proof. exact (@lem3624507 (term58 A B C h f s)). Qed.
Lemma lem3624509 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term16 A B f s t) : term58 A B C h f s.
Proof. exact (EQ_MP (@lem3624508 A B C h f s) (@lem3624505 A B C h f s t h1 h2 h3 h4)). Qed.
Lemma lem3624512 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3624514 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term396 A B C h f s) = (term545 A B C h f s).
Proof. exact (@lem3624512 (term58 A B C h f s)). Qed.
Lemma lem3624517 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (h1 : term396 A B C h f s) : term545 A B C h f s.
Proof. exact (EQ_MP (@lem3624514 A B C h f s) (@lem3624020 A B C h f s h1)). Qed.
Lemma lem3624520 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (@lem3624517 A B C h f s h4 (@lem3624509 A B C h f s t h1 h2 h3 h5)). Qed.
Lemma lem3624521 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : term358.
Proof. exact (fun h0 : ~ False => @lem3624520 A B C h f s t h1 h2 h3 h4 h5). Qed.
Lemma lem3624523 (p : Prop) : (term336 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3624524 : term358 = False.
Proof. exact (@lem3624523 False). Qed.
Lemma lem3624525 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624524) (@lem3624521 A B C h f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem3624526 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term396 A B C h f s) = False.
Proof. exact (prop_ext (fun h6 : term396 A B C h f s => @lem3624525 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3624020 A B C h f s h4)). Qed.
Lemma lem3624527 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624526 A B C h f s t h1 h2 h3 h4 h5) (@lem3624020 A B C h f s h4)). Qed.
Lemma lem3624528 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h6 : @FINITE B t => @lem3624527 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3624012 B t h3)). Qed.
Lemma lem3624529 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624528 A B C h f s t h1 h2 h3 h4 h5) (@lem3624012 B t h3)). Qed.
Lemma lem3624530 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term16 A B f s t) = False.
Proof. exact (prop_ext (fun h6 : term16 A B f s t => @lem3624529 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3624010 A B f s t h5)). Qed.
Lemma lem3624531 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624530 A B C h f s t h1 h2 h3 h4 h5) (@lem3624010 A B f s t h5)). Qed.
Lemma lem3624532 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term396 A B C h f s) = False.
Proof. exact (prop_ext (fun h6 : term396 A B C h f s => @lem3624531 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623733 A B C h f s h4)). Qed.
Lemma lem3624533 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624532 A B C h f s t h1 h2 h3 h4 h5) (@lem3623733 A B C h f s h4)). Qed.
Lemma lem3624534 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h6 : @FINITE B t => @lem3624533 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623716 B t h3)). Qed.
Lemma lem3624535 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624534 A B C h f s t h1 h2 h3 h4 h5) (@lem3623716 B t h3)). Qed.
Lemma lem3624536 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term16 A B f s t) = False.
Proof. exact (prop_ext (fun h6 : term16 A B f s t => @lem3624535 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623712 A B f s t h5)). Qed.
Lemma lem3624537 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624536 A B C h f s t h1 h2 h3 h4 h5) (@lem3623712 A B f s t h5)). Qed.
Lemma lem3624538 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term396 A B C h f s) = False.
Proof. exact (prop_ext (fun h6 : term396 A B C h f s => @lem3624537 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623733 A B C h f s h4)). Qed.
Lemma lem3624539 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624538 A B C h f s t h1 h2 h3 h4 h5) (@lem3623733 A B C h f s h4)). Qed.
Lemma lem3624540 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h6 : @FINITE B t => @lem3624539 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623716 B t h3)). Qed.
Lemma lem3624541 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624540 A B C h f s t h1 h2 h3 h4 h5) (@lem3623716 B t h3)). Qed.
Lemma lem3624542 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term16 A B f s t) = False.
Proof. exact (prop_ext (fun h6 : term16 A B f s t => @lem3624541 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623712 A B f s t h5)). Qed.
Lemma lem3624543 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624542 A B C h f s t h1 h2 h3 h4 h5) (@lem3623712 A B f s t h5)). Qed.
Lemma lem3624544 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term396 A B C h f s) = False.
Proof. exact (prop_ext (fun h6 : term396 A B C h f s => @lem3624543 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623514 A B C h f s h4)). Qed.
Lemma lem3624545 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624544 A B C h f s t h1 h2 h3 h4 h5) (@lem3623514 A B C h f s h4)). Qed.
Lemma lem3624546 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h6 : @FINITE B t => @lem3624545 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623466 B t h3)). Qed.
Lemma lem3624547 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624546 A B C h f s t h1 h2 h3 h4 h5) (@lem3623466 B t h3)). Qed.
Lemma lem3624548 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term16 A B f s t) = False.
Proof. exact (prop_ext (fun h6 : term16 A B f s t => @lem3624547 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3623462 A B f s t h5)). Qed.
Lemma lem3624549 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624548 A B C h f s t h1 h2 h3 h4 h5) (@lem3623462 A B f s t h5)). Qed.
Lemma lem3624550 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term396 A B C h f s) = False.
Proof. exact (prop_ext (fun h6 : term396 A B C h f s => @lem3624549 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3622640 A B C h f s h4)). Qed.
Lemma lem3624551 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624550 A B C h f s t h1 h2 h3 h4 h5) (@lem3622640 A B C h f s h4)). Qed.
Lemma lem3624552 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h6 : @FINITE B t => @lem3624551 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3622571 B t h3)). Qed.
Lemma lem3624553 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624552 A B C h f s t h1 h2 h3 h4 h5) (@lem3622571 B t h3)). Qed.
Lemma lem3624554 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : (term16 A B f s t) = False.
Proof. exact (prop_ext (fun h6 : term16 A B f s t => @lem3624553 A B C h f s t h1 h2 h3 h4 h5) (fun h6 : False => @lem3622565 A B f s t h5)). Qed.
Lemma lem3624555 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624554 A B C h f s t h1 h2 h3 h4 h5) (@lem3622565 A B f s t h5)). Qed.
Lemma lem3624556 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : term405 B C.
Proof. exact (fun h0 : term398 B C => @lem3624555 A B C h f s t h1 h2 h3 h4 h5). Qed.
Lemma lem3624557 {B C : Type'} : (term405 B C) = (term406 B C).
Proof. exact (@lem69 (term398 B C)). Qed.
Lemma lem3624558 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term399 B C) (h2 : term400 B) (h3 : @FINITE B t) (h4 : term396 A B C h f s) (h5 : term16 A B f s t) : term406 B C.
Proof. exact (EQ_MP (@lem3624557 B C) (@lem3624556 A B C h f s t h1 h2 h3 h4 h5)). Qed.
Lemma lem3624559 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term409 B C.
Proof. exact (fun h0 : term399 B C => @lem3624558 A B C h f s t h0 h1 h2 h3 h4). Qed.
Lemma lem3624560 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term412 B C.
Proof. exact (fun h0 : term397 B => @lem3624559 A B C h f s t h1 h2 h3 h4). Qed.
Lemma lem3624561 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term414 A B C.
Proof. exact (fun h0 : term399 A C => @lem3624560 A B C h f s t h1 h2 h3 h4). Qed.
Lemma lem3624562 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term416 A B C.
Proof. exact (fun h0 : term399 A B => @lem3624561 A B C h f s t h1 h2 h3 h4). Qed.
Lemma lem3624563 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term400 B) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term419 A B C.
Proof. exact (fun h0 : term400 C => @lem3624562 A B C h f s t h1 h2 h3 h4). Qed.
Lemma lem3624564 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term396 A B C h f s) (h3 : term16 A B f s t) : term421 A B C.
Proof. exact (fun h0 : term400 B => @lem3624563 A B C h f s t h0 h1 h2 h3). Qed.
Lemma lem3624565 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term396 A B C h f s) (h3 : term16 A B f s t) : term423 A B C.
Proof. exact (fun h0 : term400 A => @lem3624564 A B C h f s t h1 h2 h3). Qed.
Lemma lem3624566 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term16 A B f s t) : term426 A B C h f s.
Proof. exact (fun h0 : term396 A B C h f s => @lem3624565 A B C h f s t h1 h0 h2). Qed.
Lemma lem3624567 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term16 A B f s t) : term429 A B C g h f s.
Proof. exact (fun h0 : term50 A B C s g h f => @lem3624566 A B C h f s t h1 h2). Qed.
Lemma lem3624568 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term432 A B C t g h f s.
Proof. exact (fun h0 : @FINITE B t => @lem3624567 A B C g h f s t h0 h1). Qed.
Lemma lem3624569 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term434 A B C t g h f s.
Proof. exact (fun h0 : term16 A B f s t => @lem3624568 A B C g h f s t h0). Qed.
Lemma lem3624574 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term438 A B C g h f s.
Proof. exact (fun t : B -> Prop => @lem3624569 A B C t g h f s). Qed.
Lemma lem3624579 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : term442 A B C h f s.
Proof. exact (fun g : A -> C => @lem3624574 A B C g h f s). Qed.
Lemma lem3624584 {A B C : Type'} (f : A -> B) (s : A -> Prop) : term446 A B C f s.
Proof. exact (fun h : B -> C => @lem3624579 A B C h f s). Qed.
Lemma lem3624589 {A B C : Type'} (s : A -> Prop) : term450 A B C s.
Proof. exact (fun f : A -> B => @lem3624584 A B C f s). Qed.
Lemma lem3624594 {A B C : Type'} : term454 A B C.
Proof. exact (fun s : A -> Prop => @lem3624589 A B C s). Qed.
Lemma lem3624595 {A B C : Type'} : term453 A B C.
Proof. exact (EQ_MP (@lem3622547 A B C) (@lem3624594 A B C)). Qed.
Lemma lem3624596 {A B C : Type'} (s : A -> Prop) : term546 A B C s.
Proof. exact (@lem3624595 A B C s). Qed.
Lemma lem3624597 {A B C : Type'} (s : A -> Prop) : (term546 A B C s) = (term449 A B C s).
Proof. exact (eq_refl (term546 A B C s)). Qed.
Lemma lem3624598 {A B C : Type'} (s : A -> Prop) : term449 A B C s.
Proof. exact (EQ_MP (@lem3624597 A B C s) (@lem3624596 A B C s)). Qed.
Lemma lem3624599 {A B C : Type'} (s : A -> Prop) (f : A -> B) : term547 A B C s f.
Proof. exact (@lem3624598 A B C s f). Qed.
Lemma lem3624600 {A B C : Type'} (f : A -> B) (s : A -> Prop) : (term547 A B C s f) = (term445 A B C f s).
Proof. exact (eq_refl (term547 A B C s f)). Qed.
Lemma lem3624601 {A B C : Type'} (f : A -> B) (s : A -> Prop) : term445 A B C f s.
Proof. exact (EQ_MP (@lem3624600 A B C f s) (@lem3624599 A B C s f)). Qed.
Lemma lem3624602 {A B C : Type'} (f : A -> B) (s : A -> Prop) (h : B -> C) : term548 A B C f s h.
Proof. exact (@lem3624601 A B C f s h). Qed.
Lemma lem3624603 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : (term548 A B C f s h) = (term441 A B C h f s).
Proof. exact (eq_refl (term548 A B C f s h)). Qed.
Lemma lem3624604 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) : term441 A B C h f s.
Proof. exact (EQ_MP (@lem3624603 A B C h f s) (@lem3624602 A B C f s h)). Qed.
Lemma lem3624605 {A B C : Type'} (h : B -> C) (f : A -> B) (s : A -> Prop) (g : A -> C) : term549 A B C h f s g.
Proof. exact (@lem3624604 A B C h f s g). Qed.
Lemma lem3624606 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term549 A B C h f s g) = (term437 A B C g h f s).
Proof. exact (eq_refl (term549 A B C h f s g)). Qed.
Lemma lem3624607 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term437 A B C g h f s.
Proof. exact (EQ_MP (@lem3624606 A B C g h f s) (@lem3624605 A B C h f s g)). Qed.
Lemma lem3624608 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term550 A B C g h f s t.
Proof. exact (@lem3624607 A B C g h f s t). Qed.
Lemma lem3624609 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : (term550 A B C g h f s t) = (term401 A B C t g h f s).
Proof. exact (eq_refl (term550 A B C g h f s t)). Qed.
Lemma lem3624610 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term401 A B C t g h f s.
Proof. exact (EQ_MP (@lem3624609 A B C t g h f s) (@lem3624608 A B C g h f s t)). Qed.
Lemma lem3624612 {A B C : Type'} (t : B -> Prop) (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) : term401 A B C t g h f s.
Proof. exact (@lem3621982 A B C t g h f s (@lem3624610 A B C t g h f s)). Qed.
Lemma lem3624613 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term16 A B f s t) : term431 A B C t g h f s.
Proof. exact (@lem3624612 A B C t g h f s (@lem3619201 A B f s t h1)). Qed.
Lemma lem3624614 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term16 A B f s t) : term428 A B C g h f s.
Proof. exact (@lem3624613 A B C g h f s t h2 (@lem3619203 B t h1)). Qed.
Lemma lem3624615 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term425 A B C h f s.
Proof. exact (@lem3624614 A B C g h f s t h2 h3 (@lem3619244 A B C s g h f h1)). Qed.
Lemma lem3624616 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term422 A B C.
Proof. exact (@lem3624615 A B C g h f s t h1 h2 h4 (@lem3621956 A B C h f s h3)). Qed.
Lemma lem3624617 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term420 A B C.
Proof. exact (@lem3624616 A B C g h f s t h1 h2 h3 h4 (@lem3621965 A)). Qed.
Lemma lem3624618 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term418 A B C.
Proof. exact (@lem3624617 A B C g h f s t h1 h2 h3 h4 (@lem3621963 B)). Qed.
Lemma lem3624619 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term415 A B C.
Proof. exact (@lem3624618 A B C g h f s t h1 h2 h3 h4 (@lem3621964 C)). Qed.
Lemma lem3624620 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term413 A B C.
Proof. exact (@lem3624619 A B C g h f s t h1 h2 h3 h4 (@lem3621959 A B)). Qed.
Lemma lem3624621 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term411 B C.
Proof. exact (@lem3624620 A B C g h f s t h1 h2 h3 h4 (@lem3621960 A C)). Qed.
Lemma lem3624622 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term408 B C.
Proof. exact (@lem3624621 A B C g h f s t h1 h2 h3 h4 (@lem3621957 B)). Qed.
Lemma lem3624623 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : term405 B C.
Proof. exact (@lem3624622 A B C g h f s t h1 h2 h3 h4 (@lem3621962 B C)). Qed.
Lemma lem3624624 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : False.
Proof. exact (@lem3624623 A B C g h f s t h1 h2 h3 h4 (@lem3621958 B C)). Qed.
Lemma lem3624625 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : (term396 A B C h f s) = False.
Proof. exact (prop_ext (fun h5 : term396 A B C h f s => @lem3624624 A B C g h f s t h1 h2 h3 h4) (fun h5 : False => @lem3621956 A B C h f s h3)). Qed.
Lemma lem3624626 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term396 A B C h f s) (h4 : term16 A B f s t) : False.
Proof. exact (EQ_MP (@lem3624625 A B C g h f s t h1 h2 h3 h4) (@lem3621956 A B C h f s h3)). Qed.
Lemma lem3624627 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term395 A B C h f s.
Proof. exact (fun h0 : term396 A B C h f s => @lem3624626 A B C g h f s t h1 h2 h0 h3). Qed.
Lemma lem3624628 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term58 A B C h f s.
Proof. exact (EQ_MP (@lem3621955 A B C h f s) (@lem3624627 A B C g h f s t h1 h2 h3)). Qed.
Lemma lem3624629 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : (@IMAGE A C g s) = (term54 A B C h f s)) (h4 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3619258 A B C g h f s h3) (@lem3624628 A B C g h f s t h1 h2 h4)). Qed.
Lemma lem3624630 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : ((@IMAGE A C g s) = (term54 A B C h f s)) = (term60 A C g s).
Proof. exact (prop_ext (fun h4 : (@IMAGE A C g s) = (term54 A B C h f s) => @lem3624629 A B C g h f s t h1 h2 h4 h3) (fun h4 : term60 A C g s => @lem3621951 A B C g h f s t h1 h2 h3)). Qed.
Lemma lem3624631 {A B C : Type'} (g : A -> C) (h : B -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term50 A B C s g h f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624630 A B C g h f s t h1 h2 h3) (@lem3621951 A B C g h f s t h1 h2 h3)). Qed.
Lemma lem3624632 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term53 A B C s g f) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term60 A C g s.
Proof. exact (ex_elim (@lem3619243 A B C s g f h1) (fun h : B -> C => fun h0 : term52 A B C s g f h => @lem3624631 A B C g h f s t h0 h2 h3)). Qed.
Lemma lem3624633 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term16 A B f s t) : term551 A B C f g s.
Proof. exact (fun h0 : term53 A B C s g f => @lem3624632 A B C g f s t h0 h1 h2). Qed.
Lemma lem3624634 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term17 A B C s f g) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term60 A C g s.
Proof. exact (@lem3624633 A B C g f s t h2 h3 (@lem3619242 A B C s f g h1)). Qed.
Lemma lem3624635 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term14 A B C t s f g) : term15 A B C t s f g.
Proof. exact (proj2 (@lem3619199 A B C t s f g h1)). Qed.
Lemma lem3624636 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term14 A B C t s f g) : term16 A B f s t.
Proof. exact (proj1 (@lem3619199 A B C t s f g h1)). Qed.
Lemma lem3624637 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term15 A B C t s f g) : term17 A B C s f g.
Proof. exact (proj2 (@lem3619200 A B C t s f g h1)). Qed.
Lemma lem3624638 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term15 A B C t s f g) : @FINITE B t.
Proof. exact (proj1 (@lem3619200 A B C t s f g h1)). Qed.
Lemma lem3624639 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term17 A B C s f g) (h2 : @FINITE B t) (h3 : term16 A B f s t) : (term17 A B C s f g) = (term60 A C g s).
Proof. exact (prop_ext (fun h4 : term17 A B C s f g => @lem3624634 A B C g f s t h1 h2 h3) (fun h4 : term60 A C g s => @lem3619202 A B C s f g h1)). Qed.
Lemma lem3624640 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term17 A B C s f g) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624639 A B C g f s t h1 h2 h3) (@lem3619202 A B C s f g h1)). Qed.
Lemma lem3624641 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term17 A B C s f g) (h2 : @FINITE B t) (h3 : term16 A B f s t) : (@FINITE B t) = (term60 A C g s).
Proof. exact (prop_ext (fun h4 : @FINITE B t => @lem3624640 A B C g f s t h1 h2 h3) (fun h4 : term60 A C g s => @lem3619203 B t h2)). Qed.
Lemma lem3624642 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term17 A B C s f g) (h2 : @FINITE B t) (h3 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624641 A B C g f s t h1 h2 h3) (@lem3619203 B t h2)). Qed.
Lemma lem3624643 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term15 A B C t s f g) (h3 : term16 A B f s t) : (term17 A B C s f g) = (term60 A C g s).
Proof. exact (prop_ext (fun h4 : term17 A B C s f g => @lem3624642 A B C g f s t h4 h1 h3) (fun h4 : term60 A C g s => @lem3624637 A B C t s f g h2)). Qed.
Lemma lem3624644 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) (h2 : term15 A B C t s f g) (h3 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624643 A B C g f s t h1 h2 h3) (@lem3624637 A B C t s f g h2)). Qed.
Lemma lem3624645 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B C t s f g) (h2 : term16 A B f s t) : (@FINITE B t) = (term60 A C g s).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem3624644 A B C g f s t h3 h1 h2) (fun h3 : term60 A C g s => @lem3624638 A B C t s f g h1)). Qed.
Lemma lem3624646 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B C t s f g) (h2 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624645 A B C g f s t h1 h2) (@lem3624638 A B C t s f g h1)). Qed.
Lemma lem3624647 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B C t s f g) (h2 : term16 A B f s t) : (term16 A B f s t) = (term60 A C g s).
Proof. exact (prop_ext (fun h3 : term16 A B f s t => @lem3624646 A B C g f s t h1 h2) (fun h3 : term60 A C g s => @lem3619201 A B f s t h2)). Qed.
Lemma lem3624648 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B C t s f g) (h2 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624647 A B C g f s t h1 h2) (@lem3619201 A B f s t h2)). Qed.
Lemma lem3624649 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B C t s f g) (h2 : term16 A B f s t) : (term15 A B C t s f g) = (term60 A C g s).
Proof. exact (prop_ext (fun h3 : term15 A B C t s f g => @lem3624648 A B C g f s t h3 h2) (fun h3 : term60 A C g s => @lem3624635 A B C t s f g h1)). Qed.
Lemma lem3624650 {A B C : Type'} (g : A -> C) (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term14 A B C t s f g) (h2 : term16 A B f s t) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624649 A B C g f s t h1 h2) (@lem3624635 A B C t s f g h1)). Qed.
Lemma lem3624651 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term14 A B C t s f g) : (term16 A B f s t) = (term60 A C g s).
Proof. exact (prop_ext (fun h2 : term16 A B f s t => @lem3624650 A B C g f s t h1 h2) (fun h2 : term60 A C g s => @lem3624636 A B C t s f g h1)). Qed.
Lemma lem3624652 {A B C : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : A -> C) (h1 : term14 A B C t s f g) : term60 A C g s.
Proof. exact (EQ_MP (@lem3624651 A B C t s f g h1) (@lem3624636 A B C t s f g h1)). Qed.
Lemma lem3624653 {A B C : Type'} (t : B -> Prop) (f : A -> B) (g : A -> C) (s : A -> Prop) : term552 A B C t f g s.
Proof. exact (fun h0 : term14 A B C t s f g => @lem3624652 A B C t s f g h0). Qed.
Lemma lem3624658 {A B C : Type'} (f : A -> B) (g : A -> C) (s : A -> Prop) : term553 A B C f g s.
Proof. exact (fun t : B -> Prop => @lem3624653 A B C t f g s). Qed.
Lemma lem3624663 {A B C : Type'} (f : A -> B) (g : A -> C) : term554 A B C f g.
Proof. exact (fun s : A -> Prop => @lem3624658 A B C f g s). Qed.
Lemma lem3624668 {A B C : Type'} (f : A -> B) : term555 A B C f.
Proof. exact (fun g : A -> C => @lem3624663 A B C f g). Qed.
Lemma lem3624673 {A B C : Type'} : term556 A B C.
Proof. exact (fun f : A -> B => @lem3624668 A B C f). Qed.
