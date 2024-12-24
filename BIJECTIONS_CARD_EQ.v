Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIJECTIONS_CARD_EQ_term_abbrevs.
Require Import BIJECTIONS_HAS_SIZE_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem5100081 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem5100070 A B s). Qed.
Lemma lem5100082 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem5100083 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem5100082 A B s) (@lem5100081 A B s)). Qed.
Lemma lem5100084 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term2 A B s t.
Proof. exact (@lem5100083 A B s t). Qed.
Lemma lem5100085 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term2 A B s t) = (term3 A B s t).
Proof. exact (eq_refl (term2 A B s t)). Qed.
Lemma lem5100086 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term3 A B s t.
Proof. exact (EQ_MP (@lem5100085 A B s t) (@lem5100084 A B s t)). Qed.
Lemma lem5100087 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : term4 A B s t f.
Proof. exact (@lem5100086 A B s t f). Qed.
Lemma lem5100088 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term4 A B s t f) = (term5 A B f s t).
Proof. exact (eq_refl (term4 A B s t f)). Qed.
Lemma lem5100089 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term5 A B f s t.
Proof. exact (EQ_MP (@lem5100088 A B f s t) (@lem5100087 A B s t f)). Qed.
Lemma lem5100090 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) : term6 A B f s t g.
Proof. exact (@lem5100089 A B f s t g). Qed.
Lemma lem5100091 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) : (term6 A B f s t g) = (term7 A B f g s t).
Proof. exact (eq_refl (term6 A B f s t g)). Qed.
Lemma lem5100093 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term8 A B t s f g) : term8 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5100094 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term9 A B t s f g) : term9 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5100096 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) : term7 A B f g s t.
Proof. exact (EQ_MP (@lem5100091 A B f g s t) (@lem5100090 A B f s t g)). Qed.
Lemma lem5100097 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) : term7 A B f g s t.
Proof. exact (@lem5100096 A B f g s t). Qed.
Lemma lem5100098 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term9 A B t s f g) : term10 A B s t.
Proof. exact (@lem5100097 A B f g s t (@lem5100094 A B t s f g h1)). Qed.
Lemma lem5100099 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term11 A B s t) : term11 A B s t.
Proof. exact (h1). Qed.
Lemma lem5100101 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5100102 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term13 A B s t) = (term14 A B s t).
Proof. exact (@lem5100101 (term13 A B s t)). Qed.
Lemma lem5100103 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term14 A B s t) = (term13 A B s t).
Proof. exact (SYM (@lem5100102 A B s t)). Qed.
Lemma lem5100104 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term15 A B s t.
Proof. exact (h1). Qed.
Lemma lem5100105 {A : Type'} : term16 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem5100106 {B : Type'} : term16 B.
Proof. exact (@lem3863773 B). Qed.
Lemma lem5100113 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term17 _100044 A B s t) : term17 _100044 A B s t.
Proof. exact (h1). Qed.
Lemma lem5100114 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : term18 _100044 A B s t.
Proof. exact (fun h0 : term17 _100044 A B s t => @lem5100113 _100044 A B s t h0). Qed.
Lemma lem5100115 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term18 _100044 A B s t) : term18 _100044 A B s t.
Proof. exact (h1). Qed.
Lemma lem5100116 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term17 _100044 A B s t) : term17 _100044 A B s t.
Proof. exact (h1). Qed.
Lemma lem5100117 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term17 _100044 A B s t) (h2 : term18 _100044 A B s t) : term17 _100044 A B s t.
Proof. exact (@lem5100115 _100044 A B s t h2 (@lem5100116 _100044 A B s t h1)). Qed.
Lemma lem5100118 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term17 _100044 A B s t) : term19 _100044 A B s t.
Proof. exact (fun h0 : term18 _100044 A B s t => @lem5100117 _100044 A B s t h1 h0). Qed.
Lemma lem5100119 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term18 _100044 A B s t) : term18 _100044 A B s t.
Proof. exact (h1). Qed.
Lemma lem5100120 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term17 _100044 A B s t) (h2 : term18 _100044 A B s t) : term17 _100044 A B s t.
Proof. exact (@lem5100118 _100044 A B s t h1 (@lem5100119 _100044 A B s t h2)). Qed.
Lemma lem5100121 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term18 _100044 A B s t) : term18 _100044 A B s t.
Proof. exact (fun h0 : term17 _100044 A B s t => @lem5100120 _100044 A B s t h0 h1). Qed.
Lemma lem5100122 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : term20 _100044 A B s t.
Proof. exact (fun h0 : term18 _100044 A B s t => @lem5100121 _100044 A B s t h0). Qed.
Lemma lem5100125 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : term18 _100044 A B s t.
Proof. exact (@lem5100122 _100044 A B s t (@lem5100114 _100044 A B s t)). Qed.
Lemma lem5100126 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : term18 _100044 A B s t.
Proof. exact (@lem5100125 _100044 A B s t). Qed.
Lemma lem5100172 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5100173 {B : Type'} : (term21 B) = (term22 B).
Proof. exact (@lem5100172 (term16 B)). Qed.
Lemma lem5100184 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (eq_refl (term23 A)). Qed.
Lemma lem5100185 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem5100184 A) (@lem5100173 B)). Qed.
Lemma lem5100188 {_100044 : Type'} : (term23 _100044) = (term23 _100044).
Proof. exact (eq_refl (term23 _100044)). Qed.
Lemma lem5100189 {_100044 A B : Type'} : (term26 _100044 A B) = (term27 _100044 A B).
Proof. exact (MK_COMB (@lem5100188 _100044) (@lem5100185 A B)). Qed.
Lemma lem5100192 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term28 A B s t) = (term28 A B s t).
Proof. exact (eq_refl (term28 A B s t)). Qed.
Lemma lem5100193 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term17 _100044 A B s t) = (term29 _100044 A B s t).
Proof. exact (MK_COMB (@lem5100192 A B s t) (@lem5100189 _100044 A B)). Qed.
Lemma lem5100196 {_100044 A B : Type'} (t : B -> Prop) : (term30 _100044 A B t) = (term31 _100044 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5100193 _100044 A B s t)). Qed.
Lemma lem5100197 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5100198 {_100044 A B : Type'} (t : B -> Prop) : (term32 _100044 A B t) = (term33 _100044 A B t).
Proof. exact (MK_COMB (@lem5100197 A) (@lem5100196 _100044 A B t)). Qed.
Lemma lem5100203 {_100044 A B : Type'} : (term34 _100044 A B) = (term35 _100044 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5100198 _100044 A B t)). Qed.
Lemma lem5100204 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5100213 {_100044 A B : Type'} : (term36 _100044 A B) = (term37 _100044 A B).
Proof. exact (MK_COMB (@lem5100204 B) (@lem5100203 _100044 A B)). Qed.
Lemma lem5100222 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term38 B s n)) = ((@HAS_SIZE B s n) = (term38 B s n)).
Proof. exact (eq_refl ((@HAS_SIZE B s n) = (term38 B s n))). Qed.
Lemma lem5100223 {B : Type'} (s : B -> Prop) : (term39 B s) = (term39 B s).
Proof. exact (fun_ext (fun n : nat => @lem5100222 B s n)). Qed.
Lemma lem5100224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100225 {B : Type'} (s : B -> Prop) : (term40 B s) = (term40 B s).
Proof. exact (MK_COMB (@lem5100224) (@lem5100223 B s)). Qed.
Lemma lem5100226 {B : Type'} : (term41 B) = (term41 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5100225 B s)). Qed.
Lemma lem5100227 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5100228 {B : Type'} : (term16 B) = (term16 B).
Proof. exact (MK_COMB (@lem5100227 B) (@lem5100226 B)). Qed.
Lemma lem5100229 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5100230 {B : Type'} : (term22 B) = (term22 B).
Proof. exact (MK_COMB (@lem5100229) (@lem5100228 B)). Qed.
Lemma lem5100239 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term38 A s n)) = ((@HAS_SIZE A s n) = (term38 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term38 A s n))). Qed.
Lemma lem5100240 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (fun_ext (fun n : nat => @lem5100239 A s n)). Qed.
Lemma lem5100241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100242 {A : Type'} (s : A -> Prop) : (term40 A s) = (term40 A s).
Proof. exact (MK_COMB (@lem5100241) (@lem5100240 A s)). Qed.
Lemma lem5100243 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5100242 A s)). Qed.
Lemma lem5100244 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5100245 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem5100244 A) (@lem5100243 A)). Qed.
Lemma lem5100246 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5100247 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem5100246) (@lem5100245 A)). Qed.
Lemma lem5100248 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem5100247 A) (@lem5100230 B)). Qed.
Lemma lem5100257 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term38 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term38 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term38 _100044 s n))). Qed.
Lemma lem5100258 {_100044 : Type'} (s : _100044 -> Prop) : (term39 _100044 s) = (term39 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem5100257 _100044 s n)). Qed.
Lemma lem5100259 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100260 {_100044 : Type'} (s : _100044 -> Prop) : (term40 _100044 s) = (term40 _100044 s).
Proof. exact (MK_COMB (@lem5100259) (@lem5100258 _100044 s)). Qed.
Lemma lem5100261 {_100044 : Type'} : (term41 _100044) = (term41 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem5100260 _100044 s)). Qed.
Lemma lem5100262 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem5100263 {_100044 : Type'} : (term16 _100044) = (term16 _100044).
Proof. exact (MK_COMB (@lem5100262 _100044) (@lem5100261 _100044)). Qed.
Lemma lem5100264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5100265 {_100044 : Type'} : (term23 _100044) = (term23 _100044).
Proof. exact (MK_COMB (@lem5100264) (@lem5100263 _100044)). Qed.
Lemma lem5100266 {_100044 A B : Type'} : (term27 _100044 A B) = (term27 _100044 A B).
Proof. exact (MK_COMB (@lem5100265 _100044) (@lem5100248 A B)). Qed.
Lemma lem5100275 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term42 A B s t) = (term42 A B s t).
Proof. exact (eq_refl (term42 A B s t)). Qed.
Lemma lem5100280 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (@HAS_SIZE B t n)) = ((@HAS_SIZE A s n) = (@HAS_SIZE B t n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (@HAS_SIZE B t n))). Qed.
Lemma lem5100281 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term43 A B s t) = (term43 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5100280 A B s t n)). Qed.
Lemma lem5100282 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100283 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term10 A B s t) = (term10 A B s t).
Proof. exact (MK_COMB (@lem5100282) (@lem5100281 A B s t)). Qed.
Lemma lem5100284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5100285 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term44 A B s t) = (term44 A B s t).
Proof. exact (MK_COMB (@lem5100284) (@lem5100283 A B s t)). Qed.
Lemma lem5100286 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term13 A B s t) = (term13 A B s t).
Proof. exact (MK_COMB (@lem5100285 A B s t) (@lem5100275 A B s t)). Qed.
Lemma lem5100287 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5100288 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term15 A B s t) = (term15 A B s t).
Proof. exact (MK_COMB (@lem5100287) (@lem5100286 A B s t)). Qed.
Lemma lem5100289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5100290 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term28 A B s t) = (term28 A B s t).
Proof. exact (MK_COMB (@lem5100289) (@lem5100288 A B s t)). Qed.
Lemma lem5100291 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term29 _100044 A B s t) = (term29 _100044 A B s t).
Proof. exact (MK_COMB (@lem5100290 A B s t) (@lem5100266 _100044 A B)). Qed.
Lemma lem5100292 {_100044 A B : Type'} (t : B -> Prop) : (term31 _100044 A B t) = (term31 _100044 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5100291 _100044 A B s t)). Qed.
Lemma lem5100293 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5100294 {_100044 A B : Type'} (t : B -> Prop) : (term33 _100044 A B t) = (term33 _100044 A B t).
Proof. exact (MK_COMB (@lem5100293 A) (@lem5100292 _100044 A B t)). Qed.
Lemma lem5100295 {_100044 A B : Type'} : (term35 _100044 A B) = (term35 _100044 A B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5100294 _100044 A B t)). Qed.
Lemma lem5100296 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5100297 {_100044 A B : Type'} : (term37 _100044 A B) = (term37 _100044 A B).
Proof. exact (MK_COMB (@lem5100296 B) (@lem5100295 _100044 A B)). Qed.
Lemma lem5100372 {_100044 A B : Type'} : (term36 _100044 A B) = (term37 _100044 A B).
Proof. exact (TRANS (@lem5100213 _100044 A B) (@lem5100297 _100044 A B)). Qed.
Lemma lem5100373 {_100044 A B : Type'} : (term37 _100044 A B) = (term36 _100044 A B).
Proof. exact (SYM (@lem5100372 _100044 A B)). Qed.
Lemma lem5100374 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term15 A B s t.
Proof. exact (h1). Qed.
Lemma lem5100376 {A : Type'} (h1 : term16 A) : term16 A.
Proof. exact (h1). Qed.
Lemma lem5100377 {B : Type'} (h1 : term16 B) : term16 B.
Proof. exact (h1). Qed.
Lemma lem5100392 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (@HAS_SIZE B t n)) = (term45 A B s t n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (@HAS_SIZE B t n)). Qed.
Lemma lem5100393 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term43 A B s t) = (term46 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5100392 A B s t n)). Qed.
Lemma lem5100394 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100395 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term10 A B s t) = (term47 A B s t).
Proof. exact (MK_COMB (@lem5100394) (@lem5100393 A B s t)). Qed.
Lemma lem5100406 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term48 A B s t) = (term49 A B s t).
Proof. exact (@lem17362 (term11 A B s t) ((@CARD A s) = (@CARD B t))). Qed.
Lemma lem5100407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5100408 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term50 A B s t) = (term51 A B s t).
Proof. exact (MK_COMB (@lem5100407) (@lem5100395 A B s t)). Qed.
Lemma lem5100409 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term52 A B s t) = (term53 A B s t).
Proof. exact (MK_COMB (@lem5100408 A B s t) (@lem5100406 A B s t)). Qed.
Lemma lem5100410 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term15 A B s t) = (term52 A B s t).
Proof. exact (@lem17362 (term10 A B s t) (term42 A B s t)). Qed.
Lemma lem5100411 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term15 A B s t) = (term53 A B s t).
Proof. exact (TRANS (@lem5100410 A B s t) (@lem5100409 A B s t)). Qed.
Lemma lem5100413 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5100414 (P : nat -> Prop) (Q : nat -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem5100413 nat P Q). Qed.
Lemma lem5100415 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term58 A B s t) = (term59 A B s t).
Proof. exact (@lem5100414 (term60 A B s t) (term61 A B s t)). Qed.
Lemma lem5100416 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term62 A B s t n) = (term63 A B s t n).
Proof. exact (eq_refl (term62 A B s t n)). Qed.
Lemma lem5100417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5100418 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term64 A B s t n) = (term65 A B s t n).
Proof. exact (MK_COMB (@lem5100417) (@lem5100416 A B s t n)). Qed.
Lemma lem5100419 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term66 A B s t n) = (term67 A B s t n).
Proof. exact (eq_refl (term66 A B s t n)). Qed.
Lemma lem5100420 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term68 A B s t n) = (term45 A B s t n).
Proof. exact (MK_COMB (@lem5100418 A B s t n) (@lem5100419 A B s t n)). Qed.
Lemma lem5100421 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term69 A B s t) = (term46 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5100420 A B s t n)). Qed.
Lemma lem5100422 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100423 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term58 A B s t) = (term47 A B s t).
Proof. exact (MK_COMB (@lem5100422) (@lem5100421 A B s t)). Qed.
Lemma lem5100424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5100425 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term70 A B s t) = (term71 A B s t).
Proof. exact (MK_COMB (@lem5100424) (@lem5100423 A B s t)). Qed.
Lemma lem5100426 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term62 A B s t n) = (term63 A B s t n).
Proof. exact (eq_refl (term62 A B s t n)). Qed.
Lemma lem5100427 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term72 A B s t) = (term60 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5100426 A B s t n)). Qed.
Lemma lem5100428 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100429 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term73 A B s t) = (term74 A B s t).
Proof. exact (MK_COMB (@lem5100428) (@lem5100427 A B s t)). Qed.
Lemma lem5100430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5100431 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term75 A B s t) = (term76 A B s t).
Proof. exact (MK_COMB (@lem5100430) (@lem5100429 A B s t)). Qed.
Lemma lem5100432 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term66 A B s t n) = (term67 A B s t n).
Proof. exact (eq_refl (term66 A B s t n)). Qed.
Lemma lem5100433 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term77 A B s t) = (term61 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5100432 A B s t n)). Qed.
Lemma lem5100434 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100435 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term78 A B s t) = (term79 A B s t).
Proof. exact (MK_COMB (@lem5100434) (@lem5100433 A B s t)). Qed.
Lemma lem5100436 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term59 A B s t) = (term80 A B s t).
Proof. exact (MK_COMB (@lem5100431 A B s t) (@lem5100435 A B s t)). Qed.
Lemma lem5100437 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term58 A B s t) = (term59 A B s t)) = ((term47 A B s t) = (term80 A B s t)).
Proof. exact (MK_COMB (@lem5100425 A B s t) (@lem5100436 A B s t)). Qed.
Lemma lem5100438 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term47 A B s t) = (term80 A B s t).
Proof. exact (EQ_MP (@lem5100437 A B s t) (@lem5100415 A B s t)). Qed.
Lemma lem5100535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5100536 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term51 A B s t) = (term81 A B s t).
Proof. exact (MK_COMB (@lem5100535) (@lem5100438 A B s t)). Qed.
Lemma lem5100537 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term49 A B s t) = (term49 A B s t).
Proof. exact (eq_refl (term49 A B s t)). Qed.
Lemma lem5100540 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term53 A B s t) = (term82 A B s t).
Proof. exact (MK_COMB (@lem5100536 A B s t) (@lem5100537 A B s t)). Qed.
Lemma lem5100541 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term15 A B s t) = (term82 A B s t).
Proof. exact (TRANS (@lem5100411 A B s t) (@lem5100540 A B s t)). Qed.
Lemma lem5100542 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term82 A B s t.
Proof. exact (EQ_MP (@lem5100541 A B s t) (@lem5100374 A B s t h1)). Qed.
Lemma lem5100850 {A : Type'} (s : A -> Prop) (n : nat) : (term83 A s n) = (term84 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem5100856 {A : Type'} (s : A -> Prop) (n : nat) : (term85 A s n) = (term85 A s n).
Proof. exact (eq_refl (term85 A s n)). Qed.
Lemma lem5100858 {A : Type'} (s : A -> Prop) (n : nat) : (term86 A s n) = (term86 A s n).
Proof. exact (eq_refl (term86 A s n)). Qed.
Lemma lem5100859 {A : Type'} (s : A -> Prop) (n : nat) : (term87 A s n) = (term88 A s n).
Proof. exact (MK_COMB (@lem5100858 A s n) (@lem5100850 A s n)). Qed.
Lemma lem5100860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5100861 {A : Type'} (s : A -> Prop) (n : nat) : (term89 A s n) = (term90 A s n).
Proof. exact (MK_COMB (@lem5100860) (@lem5100859 A s n)). Qed.
Lemma lem5100862 {A : Type'} (s : A -> Prop) (n : nat) : (term91 A s n) = (term92 A s n).
Proof. exact (MK_COMB (@lem5100861 A s n) (@lem5100856 A s n)). Qed.
Lemma lem5100863 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term38 A s n)) = (term91 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term38 A s n)). Qed.
Lemma lem5100864 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term38 A s n)) = (term92 A s n).
Proof. exact (TRANS (@lem5100863 A s n) (@lem5100862 A s n)). Qed.
Lemma lem5100865 {A : Type'} (s : A -> Prop) : (term39 A s) = (term93 A s).
Proof. exact (fun_ext (fun n : nat => @lem5100864 A s n)). Qed.
Lemma lem5100866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100867 {A : Type'} (s : A -> Prop) : (term40 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem5100866) (@lem5100865 A s)). Qed.
Lemma lem5100868 {A : Type'} : (term41 A) = (term95 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5100867 A s)). Qed.
Lemma lem5100869 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5100870 {A : Type'} : (term16 A) = (term96 A).
Proof. exact (MK_COMB (@lem5100869 A) (@lem5100868 A)). Qed.
Lemma lem5100876 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5100877 (P : nat -> Prop) (Q : nat -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem5100876 nat P Q). Qed.
Lemma lem5100878 {A : Type'} (s : A -> Prop) : (term97 A s) = (term98 A s).
Proof. exact (@lem5100877 (term99 A s) (term100 A s)). Qed.
Lemma lem5100879 {A : Type'} (s : A -> Prop) (n : nat) : (term101 A s n) = (term88 A s n).
Proof. exact (eq_refl (term101 A s n)). Qed.
Lemma lem5100880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5100881 {A : Type'} (s : A -> Prop) (n : nat) : (term102 A s n) = (term90 A s n).
Proof. exact (MK_COMB (@lem5100880) (@lem5100879 A s n)). Qed.
Lemma lem5100882 {A : Type'} (s : A -> Prop) (n : nat) : (term103 A s n) = (term85 A s n).
Proof. exact (eq_refl (term103 A s n)). Qed.
Lemma lem5100883 {A : Type'} (s : A -> Prop) (n : nat) : (term104 A s n) = (term92 A s n).
Proof. exact (MK_COMB (@lem5100881 A s n) (@lem5100882 A s n)). Qed.
Lemma lem5100884 {A : Type'} (s : A -> Prop) : (term105 A s) = (term93 A s).
Proof. exact (fun_ext (fun n : nat => @lem5100883 A s n)). Qed.
Lemma lem5100885 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100886 {A : Type'} (s : A -> Prop) : (term97 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem5100885) (@lem5100884 A s)). Qed.
Lemma lem5100887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5100888 {A : Type'} (s : A -> Prop) : (term106 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem5100887) (@lem5100886 A s)). Qed.
Lemma lem5100889 {A : Type'} (s : A -> Prop) (n : nat) : (term101 A s n) = (term88 A s n).
Proof. exact (eq_refl (term101 A s n)). Qed.
Lemma lem5100890 {A : Type'} (s : A -> Prop) : (term108 A s) = (term99 A s).
Proof. exact (fun_ext (fun n : nat => @lem5100889 A s n)). Qed.
Lemma lem5100891 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100892 {A : Type'} (s : A -> Prop) : (term109 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem5100891) (@lem5100890 A s)). Qed.
Lemma lem5100893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5100894 {A : Type'} (s : A -> Prop) : (term111 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem5100893) (@lem5100892 A s)). Qed.
Lemma lem5100895 {A : Type'} (s : A -> Prop) (n : nat) : (term103 A s n) = (term85 A s n).
Proof. exact (eq_refl (term103 A s n)). Qed.
Lemma lem5100896 {A : Type'} (s : A -> Prop) : (term113 A s) = (term100 A s).
Proof. exact (fun_ext (fun n : nat => @lem5100895 A s n)). Qed.
Lemma lem5100897 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5100898 {A : Type'} (s : A -> Prop) : (term114 A s) = (term115 A s).
Proof. exact (MK_COMB (@lem5100897) (@lem5100896 A s)). Qed.
Lemma lem5100899 {A : Type'} (s : A -> Prop) : (term98 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem5100894 A s) (@lem5100898 A s)). Qed.
Lemma lem5100900 {A : Type'} (s : A -> Prop) : ((term97 A s) = (term98 A s)) = ((term94 A s) = (term116 A s)).
Proof. exact (MK_COMB (@lem5100888 A s) (@lem5100899 A s)). Qed.
Lemma lem5100901 {A : Type'} (s : A -> Prop) : (term94 A s) = (term116 A s).
Proof. exact (EQ_MP (@lem5100900 A s) (@lem5100878 A s)). Qed.
Lemma lem5100998 {A : Type'} : (term95 A) = (term117 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5100901 A s)). Qed.
Lemma lem5100999 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101000 {A : Type'} : (term96 A) = (term118 A).
Proof. exact (MK_COMB (@lem5100999 A) (@lem5100998 A)). Qed.
Lemma lem5101002 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5101003 {A : Type'} (P : type686 A) (Q : type686 A) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem5101002 (A -> Prop) P Q). Qed.
Lemma lem5101004 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (@lem5101003 A (term123 A) (term124 A)). Qed.
Lemma lem5101005 {A : Type'} (s : A -> Prop) : (term125 A s) = (term110 A s).
Proof. exact (eq_refl (term125 A s)). Qed.
Lemma lem5101006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101007 {A : Type'} (s : A -> Prop) : (term126 A s) = (term112 A s).
Proof. exact (MK_COMB (@lem5101006) (@lem5101005 A s)). Qed.
Lemma lem5101008 {A : Type'} (s : A -> Prop) : (term127 A s) = (term115 A s).
Proof. exact (eq_refl (term127 A s)). Qed.
Lemma lem5101009 {A : Type'} (s : A -> Prop) : (term128 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem5101007 A s) (@lem5101008 A s)). Qed.
Lemma lem5101010 {A : Type'} : (term129 A) = (term117 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5101009 A s)). Qed.
Lemma lem5101011 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101012 {A : Type'} : (term121 A) = (term118 A).
Proof. exact (MK_COMB (@lem5101011 A) (@lem5101010 A)). Qed.
Lemma lem5101013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5101014 {A : Type'} : (term130 A) = (term131 A).
Proof. exact (MK_COMB (@lem5101013) (@lem5101012 A)). Qed.
Lemma lem5101015 {A : Type'} (s : A -> Prop) : (term125 A s) = (term110 A s).
Proof. exact (eq_refl (term125 A s)). Qed.
Lemma lem5101016 {A : Type'} : (term132 A) = (term123 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5101015 A s)). Qed.
Lemma lem5101017 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101018 {A : Type'} : (term133 A) = (term134 A).
Proof. exact (MK_COMB (@lem5101017 A) (@lem5101016 A)). Qed.
Lemma lem5101019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101020 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (MK_COMB (@lem5101019) (@lem5101018 A)). Qed.
Lemma lem5101021 {A : Type'} (s : A -> Prop) : (term127 A s) = (term115 A s).
Proof. exact (eq_refl (term127 A s)). Qed.
Lemma lem5101022 {A : Type'} : (term137 A) = (term124 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5101021 A s)). Qed.
Lemma lem5101023 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101024 {A : Type'} : (term138 A) = (term139 A).
Proof. exact (MK_COMB (@lem5101023 A) (@lem5101022 A)). Qed.
Lemma lem5101025 {A : Type'} : (term122 A) = (term140 A).
Proof. exact (MK_COMB (@lem5101020 A) (@lem5101024 A)). Qed.
Lemma lem5101026 {A : Type'} : ((term121 A) = (term122 A)) = ((term118 A) = (term140 A)).
Proof. exact (MK_COMB (@lem5101014 A) (@lem5101025 A)). Qed.
Lemma lem5101027 {A : Type'} : (term118 A) = (term140 A).
Proof. exact (EQ_MP (@lem5101026 A) (@lem5101004 A)). Qed.
Lemma lem5101134 {A : Type'} : (term96 A) = (term140 A).
Proof. exact (TRANS (@lem5101000 A) (@lem5101027 A)). Qed.
Lemma lem5101135 {A : Type'} : (term16 A) = (term140 A).
Proof. exact (TRANS (@lem5100870 A) (@lem5101134 A)). Qed.
Lemma lem5101136 {A : Type'} (h1 : term16 A) : term140 A.
Proof. exact (EQ_MP (@lem5101135 A) (@lem5100376 A h1)). Qed.
Lemma lem5101147 {B : Type'} (s : B -> Prop) (n : nat) : (term83 B s n) = (term84 B s n).
Proof. exact (@lem17045 (@FINITE B s) ((@CARD B s) = n)). Qed.
Lemma lem5101153 {B : Type'} (s : B -> Prop) (n : nat) : (term85 B s n) = (term85 B s n).
Proof. exact (eq_refl (term85 B s n)). Qed.
Lemma lem5101155 {B : Type'} (s : B -> Prop) (n : nat) : (term86 B s n) = (term86 B s n).
Proof. exact (eq_refl (term86 B s n)). Qed.
Lemma lem5101156 {B : Type'} (s : B -> Prop) (n : nat) : (term87 B s n) = (term88 B s n).
Proof. exact (MK_COMB (@lem5101155 B s n) (@lem5101147 B s n)). Qed.
Lemma lem5101157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101158 {B : Type'} (s : B -> Prop) (n : nat) : (term89 B s n) = (term90 B s n).
Proof. exact (MK_COMB (@lem5101157) (@lem5101156 B s n)). Qed.
Lemma lem5101159 {B : Type'} (s : B -> Prop) (n : nat) : (term91 B s n) = (term92 B s n).
Proof. exact (MK_COMB (@lem5101158 B s n) (@lem5101153 B s n)). Qed.
Lemma lem5101160 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term38 B s n)) = (term91 B s n).
Proof. exact (@lem17784 (@HAS_SIZE B s n) (term38 B s n)). Qed.
Lemma lem5101161 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term38 B s n)) = (term92 B s n).
Proof. exact (TRANS (@lem5101160 B s n) (@lem5101159 B s n)). Qed.
Lemma lem5101162 {B : Type'} (s : B -> Prop) : (term39 B s) = (term93 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101161 B s n)). Qed.
Lemma lem5101163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101164 {B : Type'} (s : B -> Prop) : (term40 B s) = (term94 B s).
Proof. exact (MK_COMB (@lem5101163) (@lem5101162 B s)). Qed.
Lemma lem5101165 {B : Type'} : (term41 B) = (term95 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101164 B s)). Qed.
Lemma lem5101166 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101167 {B : Type'} : (term16 B) = (term96 B).
Proof. exact (MK_COMB (@lem5101166 B) (@lem5101165 B)). Qed.
Lemma lem5101173 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5101174 (P : nat -> Prop) (Q : nat -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem5101173 nat P Q). Qed.
Lemma lem5101175 {B : Type'} (s : B -> Prop) : (term97 B s) = (term98 B s).
Proof. exact (@lem5101174 (term99 B s) (term100 B s)). Qed.
Lemma lem5101176 {B : Type'} (s : B -> Prop) (n : nat) : (term101 B s n) = (term88 B s n).
Proof. exact (eq_refl (term101 B s n)). Qed.
Lemma lem5101177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101178 {B : Type'} (s : B -> Prop) (n : nat) : (term102 B s n) = (term90 B s n).
Proof. exact (MK_COMB (@lem5101177) (@lem5101176 B s n)). Qed.
Lemma lem5101179 {B : Type'} (s : B -> Prop) (n : nat) : (term103 B s n) = (term85 B s n).
Proof. exact (eq_refl (term103 B s n)). Qed.
Lemma lem5101180 {B : Type'} (s : B -> Prop) (n : nat) : (term104 B s n) = (term92 B s n).
Proof. exact (MK_COMB (@lem5101178 B s n) (@lem5101179 B s n)). Qed.
Lemma lem5101181 {B : Type'} (s : B -> Prop) : (term105 B s) = (term93 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101180 B s n)). Qed.
Lemma lem5101182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101183 {B : Type'} (s : B -> Prop) : (term97 B s) = (term94 B s).
Proof. exact (MK_COMB (@lem5101182) (@lem5101181 B s)). Qed.
Lemma lem5101184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5101185 {B : Type'} (s : B -> Prop) : (term106 B s) = (term107 B s).
Proof. exact (MK_COMB (@lem5101184) (@lem5101183 B s)). Qed.
Lemma lem5101186 {B : Type'} (s : B -> Prop) (n : nat) : (term101 B s n) = (term88 B s n).
Proof. exact (eq_refl (term101 B s n)). Qed.
Lemma lem5101187 {B : Type'} (s : B -> Prop) : (term108 B s) = (term99 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101186 B s n)). Qed.
Lemma lem5101188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101189 {B : Type'} (s : B -> Prop) : (term109 B s) = (term110 B s).
Proof. exact (MK_COMB (@lem5101188) (@lem5101187 B s)). Qed.
Lemma lem5101190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101191 {B : Type'} (s : B -> Prop) : (term111 B s) = (term112 B s).
Proof. exact (MK_COMB (@lem5101190) (@lem5101189 B s)). Qed.
Lemma lem5101192 {B : Type'} (s : B -> Prop) (n : nat) : (term103 B s n) = (term85 B s n).
Proof. exact (eq_refl (term103 B s n)). Qed.
Lemma lem5101193 {B : Type'} (s : B -> Prop) : (term113 B s) = (term100 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101192 B s n)). Qed.
Lemma lem5101194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101195 {B : Type'} (s : B -> Prop) : (term114 B s) = (term115 B s).
Proof. exact (MK_COMB (@lem5101194) (@lem5101193 B s)). Qed.
Lemma lem5101196 {B : Type'} (s : B -> Prop) : (term98 B s) = (term116 B s).
Proof. exact (MK_COMB (@lem5101191 B s) (@lem5101195 B s)). Qed.
Lemma lem5101197 {B : Type'} (s : B -> Prop) : ((term97 B s) = (term98 B s)) = ((term94 B s) = (term116 B s)).
Proof. exact (MK_COMB (@lem5101185 B s) (@lem5101196 B s)). Qed.
Lemma lem5101198 {B : Type'} (s : B -> Prop) : (term94 B s) = (term116 B s).
Proof. exact (EQ_MP (@lem5101197 B s) (@lem5101175 B s)). Qed.
Lemma lem5101295 {B : Type'} : (term95 B) = (term117 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101198 B s)). Qed.
Lemma lem5101296 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101297 {B : Type'} : (term96 B) = (term118 B).
Proof. exact (MK_COMB (@lem5101296 B) (@lem5101295 B)). Qed.
Lemma lem5101299 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5101300 {B : Type'} (P : type686 B) (Q : type686 B) : (term119 B P Q) = (term120 B P Q).
Proof. exact (@lem5101299 (B -> Prop) P Q). Qed.
Lemma lem5101301 {B : Type'} : (term121 B) = (term122 B).
Proof. exact (@lem5101300 B (term123 B) (term124 B)). Qed.
Lemma lem5101302 {B : Type'} (s : B -> Prop) : (term125 B s) = (term110 B s).
Proof. exact (eq_refl (term125 B s)). Qed.
Lemma lem5101303 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101304 {B : Type'} (s : B -> Prop) : (term126 B s) = (term112 B s).
Proof. exact (MK_COMB (@lem5101303) (@lem5101302 B s)). Qed.
Lemma lem5101305 {B : Type'} (s : B -> Prop) : (term127 B s) = (term115 B s).
Proof. exact (eq_refl (term127 B s)). Qed.
Lemma lem5101306 {B : Type'} (s : B -> Prop) : (term128 B s) = (term116 B s).
Proof. exact (MK_COMB (@lem5101304 B s) (@lem5101305 B s)). Qed.
Lemma lem5101307 {B : Type'} : (term129 B) = (term117 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101306 B s)). Qed.
Lemma lem5101308 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101309 {B : Type'} : (term121 B) = (term118 B).
Proof. exact (MK_COMB (@lem5101308 B) (@lem5101307 B)). Qed.
Lemma lem5101310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5101311 {B : Type'} : (term130 B) = (term131 B).
Proof. exact (MK_COMB (@lem5101310) (@lem5101309 B)). Qed.
Lemma lem5101312 {B : Type'} (s : B -> Prop) : (term125 B s) = (term110 B s).
Proof. exact (eq_refl (term125 B s)). Qed.
Lemma lem5101313 {B : Type'} : (term132 B) = (term123 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101312 B s)). Qed.
Lemma lem5101314 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101315 {B : Type'} : (term133 B) = (term134 B).
Proof. exact (MK_COMB (@lem5101314 B) (@lem5101313 B)). Qed.
Lemma lem5101316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101317 {B : Type'} : (term135 B) = (term136 B).
Proof. exact (MK_COMB (@lem5101316) (@lem5101315 B)). Qed.
Lemma lem5101318 {B : Type'} (s : B -> Prop) : (term127 B s) = (term115 B s).
Proof. exact (eq_refl (term127 B s)). Qed.
Lemma lem5101319 {B : Type'} : (term137 B) = (term124 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101318 B s)). Qed.
Lemma lem5101320 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101321 {B : Type'} : (term138 B) = (term139 B).
Proof. exact (MK_COMB (@lem5101320 B) (@lem5101319 B)). Qed.
Lemma lem5101322 {B : Type'} : (term122 B) = (term140 B).
Proof. exact (MK_COMB (@lem5101317 B) (@lem5101321 B)). Qed.
Lemma lem5101323 {B : Type'} : ((term121 B) = (term122 B)) = ((term118 B) = (term140 B)).
Proof. exact (MK_COMB (@lem5101311 B) (@lem5101322 B)). Qed.
Lemma lem5101324 {B : Type'} : (term118 B) = (term140 B).
Proof. exact (EQ_MP (@lem5101323 B) (@lem5101301 B)). Qed.
Lemma lem5101431 {B : Type'} : (term96 B) = (term140 B).
Proof. exact (TRANS (@lem5101297 B) (@lem5101324 B)). Qed.
Lemma lem5101432 {B : Type'} : (term16 B) = (term140 B).
Proof. exact (TRANS (@lem5101167 B) (@lem5101431 B)). Qed.
Lemma lem5101433 {B : Type'} (h1 : term16 B) : term140 B.
Proof. exact (EQ_MP (@lem5101432 B) (@lem5100377 B h1)). Qed.
Lemma lem5101456 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term49 A B s t) = (term49 A B s t).
Proof. exact (eq_refl (term49 A B s t)). Qed.
Lemma lem5101471 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term67 A B s t n) = (term67 A B s t n).
Proof. exact (eq_refl (term67 A B s t n)). Qed.
Lemma lem5101472 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term61 A B s t) = (term61 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5101471 A B s t n)). Qed.
Lemma lem5101473 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101474 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term79 A B s t) = (term79 A B s t).
Proof. exact (MK_COMB (@lem5101473) (@lem5101472 A B s t)). Qed.
Lemma lem5101489 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term63 A B s t n) = (term63 A B s t n).
Proof. exact (eq_refl (term63 A B s t n)). Qed.
Lemma lem5101490 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term60 A B s t) = (term60 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5101489 A B s t n)). Qed.
Lemma lem5101491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101492 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term74 A B s t) = (term74 A B s t).
Proof. exact (MK_COMB (@lem5101491) (@lem5101490 A B s t)). Qed.
Lemma lem5101493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101494 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term76 A B s t) = (term76 A B s t).
Proof. exact (MK_COMB (@lem5101493) (@lem5101492 A B s t)). Qed.
Lemma lem5101495 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term80 A B s t) = (term80 A B s t).
Proof. exact (MK_COMB (@lem5101494 A B s t) (@lem5101474 A B s t)). Qed.
Lemma lem5101496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101497 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term81 A B s t) = (term81 A B s t).
Proof. exact (MK_COMB (@lem5101496) (@lem5101495 A B s t)). Qed.
Lemma lem5101498 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term82 A B s t) = (term82 A B s t).
Proof. exact (MK_COMB (@lem5101497 A B s t) (@lem5101456 A B s t)). Qed.
Lemma lem5101499 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term82 A B s t.
Proof. exact (EQ_MP (@lem5101498 A B s t) (@lem5100542 A B s t h1)). Qed.
Lemma lem5101586 {A : Type'} (s : A -> Prop) (n : nat) : (term85 A s n) = (term85 A s n).
Proof. exact (eq_refl (term85 A s n)). Qed.
Lemma lem5101587 {A : Type'} (s : A -> Prop) : (term100 A s) = (term100 A s).
Proof. exact (fun_ext (fun n : nat => @lem5101586 A s n)). Qed.
Lemma lem5101588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101589 {A : Type'} (s : A -> Prop) : (term115 A s) = (term115 A s).
Proof. exact (MK_COMB (@lem5101588) (@lem5101587 A s)). Qed.
Lemma lem5101590 {A : Type'} : (term124 A) = (term124 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5101589 A s)). Qed.
Lemma lem5101591 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101592 {A : Type'} : (term139 A) = (term139 A).
Proof. exact (MK_COMB (@lem5101591 A) (@lem5101590 A)). Qed.
Lemma lem5101617 {A : Type'} (s : A -> Prop) (n : nat) : (term88 A s n) = (term88 A s n).
Proof. exact (eq_refl (term88 A s n)). Qed.
Lemma lem5101618 {A : Type'} (s : A -> Prop) : (term99 A s) = (term99 A s).
Proof. exact (fun_ext (fun n : nat => @lem5101617 A s n)). Qed.
Lemma lem5101619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101620 {A : Type'} (s : A -> Prop) : (term110 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem5101619) (@lem5101618 A s)). Qed.
Lemma lem5101621 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5101620 A s)). Qed.
Lemma lem5101622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101623 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (MK_COMB (@lem5101622 A) (@lem5101621 A)). Qed.
Lemma lem5101624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101625 {A : Type'} : (term136 A) = (term136 A).
Proof. exact (MK_COMB (@lem5101624) (@lem5101623 A)). Qed.
Lemma lem5101626 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (MK_COMB (@lem5101625 A) (@lem5101592 A)). Qed.
Lemma lem5101627 {A : Type'} (h1 : term16 A) : term140 A.
Proof. exact (EQ_MP (@lem5101626 A) (@lem5101136 A h1)). Qed.
Lemma lem5101650 {B : Type'} (s : B -> Prop) (n : nat) : (term85 B s n) = (term85 B s n).
Proof. exact (eq_refl (term85 B s n)). Qed.
Lemma lem5101651 {B : Type'} (s : B -> Prop) : (term100 B s) = (term100 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101650 B s n)). Qed.
Lemma lem5101652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101653 {B : Type'} (s : B -> Prop) : (term115 B s) = (term115 B s).
Proof. exact (MK_COMB (@lem5101652) (@lem5101651 B s)). Qed.
Lemma lem5101654 {B : Type'} : (term124 B) = (term124 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101653 B s)). Qed.
Lemma lem5101655 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101656 {B : Type'} : (term139 B) = (term139 B).
Proof. exact (MK_COMB (@lem5101655 B) (@lem5101654 B)). Qed.
Lemma lem5101681 {B : Type'} (s : B -> Prop) (n : nat) : (term88 B s n) = (term88 B s n).
Proof. exact (eq_refl (term88 B s n)). Qed.
Lemma lem5101682 {B : Type'} (s : B -> Prop) : (term99 B s) = (term99 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101681 B s n)). Qed.
Lemma lem5101683 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101684 {B : Type'} (s : B -> Prop) : (term110 B s) = (term110 B s).
Proof. exact (MK_COMB (@lem5101683) (@lem5101682 B s)). Qed.
Lemma lem5101685 {B : Type'} : (term123 B) = (term123 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101684 B s)). Qed.
Lemma lem5101686 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101687 {B : Type'} : (term134 B) = (term134 B).
Proof. exact (MK_COMB (@lem5101686 B) (@lem5101685 B)). Qed.
Lemma lem5101688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5101689 {B : Type'} : (term136 B) = (term136 B).
Proof. exact (MK_COMB (@lem5101688) (@lem5101687 B)). Qed.
Lemma lem5101690 {B : Type'} : (term140 B) = (term140 B).
Proof. exact (MK_COMB (@lem5101689 B) (@lem5101656 B)). Qed.
Lemma lem5101691 {B : Type'} (h1 : term16 B) : term140 B.
Proof. exact (EQ_MP (@lem5101690 B) (@lem5101433 B h1)). Qed.
Lemma lem5101692 {B : Type'} (h1 : term16 B) : term139 B.
Proof. exact (proj2 (@lem5101691 B h1)). Qed.
Lemma lem5101693 {B : Type'} (h1 : term16 B) : term134 B.
Proof. exact (proj1 (@lem5101691 B h1)). Qed.
Lemma lem5101694 {A : Type'} (h1 : term16 A) : term139 A.
Proof. exact (proj2 (@lem5101627 A h1)). Qed.
Lemma lem5101695 {A : Type'} (h1 : term16 A) : term134 A.
Proof. exact (proj1 (@lem5101627 A h1)). Qed.
Lemma lem5101698 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term49 A B s t.
Proof. exact (proj2 (@lem5101499 A B s t h1)). Qed.
Lemma lem5101699 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term80 A B s t.
Proof. exact (proj1 (@lem5101499 A B s t h1)). Qed.
Lemma lem5101701 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term11 A B s t.
Proof. exact (proj1 (@lem5101698 A B s t h1)). Qed.
Lemma lem5101702 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term79 A B s t.
Proof. exact (proj2 (@lem5101699 A B s t h1)). Qed.
Lemma lem5101703 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term74 A B s t.
Proof. exact (proj1 (@lem5101699 A B s t h1)). Qed.
Lemma lem5101745 {B : Type'} (s : B -> Prop) (n : nat) : (term85 B s n) = (term141 B s n).
Proof. exact (@lem19490 (@FINITE B s) (term142 B s n) ((@CARD B s) = n)). Qed.
Lemma lem5101746 {B : Type'} (s : B -> Prop) : (term100 B s) = (term143 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101745 B s n)). Qed.
Lemma lem5101747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101748 {B : Type'} (s : B -> Prop) : (term115 B s) = (term144 B s).
Proof. exact (MK_COMB (@lem5101747) (@lem5101746 B s)). Qed.
Lemma lem5101749 {B : Type'} : (term124 B) = (term145 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101748 B s)). Qed.
Lemma lem5101750 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101752 {B : Type'} : (term139 B) = (term146 B).
Proof. exact (MK_COMB (@lem5101750 B) (@lem5101749 B)). Qed.
Lemma lem5101753 {B : Type'} (h1 : term16 B) : term146 B.
Proof. exact (EQ_MP (@lem5101752 B) (@lem5101692 B h1)). Qed.
Lemma lem5101767 {A : Type'} (s : A -> Prop) (n : nat) : (term88 A s n) = (term88 A s n).
Proof. exact (eq_refl (term88 A s n)). Qed.
Lemma lem5101768 {A : Type'} (s : A -> Prop) : (term99 A s) = (term99 A s).
Proof. exact (fun_ext (fun n : nat => @lem5101767 A s n)). Qed.
Lemma lem5101769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101770 {A : Type'} (s : A -> Prop) : (term110 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem5101769) (@lem5101768 A s)). Qed.
Lemma lem5101771 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5101770 A s)). Qed.
Lemma lem5101772 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101774 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (MK_COMB (@lem5101772 A) (@lem5101771 A)). Qed.
Lemma lem5101775 {A : Type'} (h1 : term16 A) : term134 A.
Proof. exact (EQ_MP (@lem5101774 A) (@lem5101695 A h1)). Qed.
Lemma lem5101874 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term67 A B s t n) = (term67 A B s t n).
Proof. exact (eq_refl (term67 A B s t n)). Qed.
Lemma lem5101875 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term61 A B s t) = (term61 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5101874 A B s t n)). Qed.
Lemma lem5101876 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101878 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term79 A B s t) = (term79 A B s t).
Proof. exact (MK_COMB (@lem5101876) (@lem5101875 A B s t)). Qed.
Lemma lem5101879 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term79 A B s t.
Proof. exact (EQ_MP (@lem5101878 A B s t) (@lem5101702 A B s t h1)). Qed.
Lemma lem5101883 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5101897 {B : Type'} (s : B -> Prop) (n : nat) : (term88 B s n) = (term88 B s n).
Proof. exact (eq_refl (term88 B s n)). Qed.
Lemma lem5101898 {B : Type'} (s : B -> Prop) : (term99 B s) = (term99 B s).
Proof. exact (fun_ext (fun n : nat => @lem5101897 B s n)). Qed.
Lemma lem5101899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101900 {B : Type'} (s : B -> Prop) : (term110 B s) = (term110 B s).
Proof. exact (MK_COMB (@lem5101899) (@lem5101898 B s)). Qed.
Lemma lem5101901 {B : Type'} : (term123 B) = (term123 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem5101900 B s)). Qed.
Lemma lem5101902 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5101904 {B : Type'} : (term134 B) = (term134 B).
Proof. exact (MK_COMB (@lem5101902 B) (@lem5101901 B)). Qed.
Lemma lem5101905 {B : Type'} (h1 : term16 B) : term134 B.
Proof. exact (EQ_MP (@lem5101904 B) (@lem5101693 B h1)). Qed.
Lemma lem5101971 {A : Type'} (s : A -> Prop) (n : nat) : (term85 A s n) = (term141 A s n).
Proof. exact (@lem19490 (@FINITE A s) (term142 A s n) ((@CARD A s) = n)). Qed.
Lemma lem5101972 {A : Type'} (s : A -> Prop) : (term100 A s) = (term143 A s).
Proof. exact (fun_ext (fun n : nat => @lem5101971 A s n)). Qed.
Lemma lem5101973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5101974 {A : Type'} (s : A -> Prop) : (term115 A s) = (term144 A s).
Proof. exact (MK_COMB (@lem5101973) (@lem5101972 A s)). Qed.
Lemma lem5101975 {A : Type'} : (term124 A) = (term145 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5101974 A s)). Qed.
Lemma lem5101976 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5101978 {A : Type'} : (term139 A) = (term146 A).
Proof. exact (MK_COMB (@lem5101976 A) (@lem5101975 A)). Qed.
Lemma lem5101979 {A : Type'} (h1 : term16 A) : term146 A.
Proof. exact (EQ_MP (@lem5101978 A) (@lem5101694 A h1)). Qed.
Lemma lem5102039 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term63 A B s t n) = (term63 A B s t n).
Proof. exact (eq_refl (term63 A B s t n)). Qed.
Lemma lem5102040 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term60 A B s t) = (term60 A B s t).
Proof. exact (fun_ext (fun n : nat => @lem5102039 A B s t n)). Qed.
Lemma lem5102041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5102043 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term74 A B s t) = (term74 A B s t).
Proof. exact (MK_COMB (@lem5102041) (@lem5102040 A B s t)). Qed.
Lemma lem5102044 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term74 A B s t.
Proof. exact (EQ_MP (@lem5102043 A B s t) (@lem5101703 A B s t h1)). Qed.
Lemma lem5102061 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem5102068 {B : Type'} (_66459 : B -> Prop) (h1 : term16 B) : term147 B _66459.
Proof. exact (@lem5101753 B h1 _66459). Qed.
Lemma lem5102069 {B : Type'} (_66459 : B -> Prop) : (term147 B _66459) = (term144 B _66459).
Proof. exact (eq_refl (term147 B _66459)). Qed.
Lemma lem5102070 {B : Type'} (_66459 : B -> Prop) (h1 : term16 B) : term144 B _66459.
Proof. exact (EQ_MP (@lem5102069 B _66459) (@lem5102068 B _66459 h1)). Qed.
Lemma lem5102071 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) (h1 : term16 B) : term148 B _66459 _66460.
Proof. exact (@lem5102070 B _66459 h1 _66460). Qed.
Lemma lem5102072 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term148 B _66459 _66460) = (term141 B _66459 _66460).
Proof. exact (eq_refl (term148 B _66459 _66460)). Qed.
Lemma lem5102073 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) (h1 : term16 B) : term141 B _66459 _66460.
Proof. exact (EQ_MP (@lem5102072 B _66459 _66460) (@lem5102071 B _66459 _66460 h1)). Qed.
Lemma lem5102074 {A : Type'} (_66461 : A -> Prop) (h1 : term16 A) : term125 A _66461.
Proof. exact (@lem5101775 A h1 _66461). Qed.
Lemma lem5102075 {A : Type'} (_66461 : A -> Prop) : (term125 A _66461) = (term110 A _66461).
Proof. exact (eq_refl (term125 A _66461)). Qed.
Lemma lem5102076 {A : Type'} (_66461 : A -> Prop) (h1 : term16 A) : term110 A _66461.
Proof. exact (EQ_MP (@lem5102075 A _66461) (@lem5102074 A _66461 h1)). Qed.
Lemma lem5102077 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) (h1 : term16 A) : term101 A _66461 _66462.
Proof. exact (@lem5102076 A _66461 h1 _66462). Qed.
Lemma lem5102078 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term101 A _66461 _66462) = (term88 A _66461 _66462).
Proof. exact (eq_refl (term101 A _66461 _66462)). Qed.
Lemma lem5102101 {A B : Type'} (_66470 : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term66 A B s t _66470.
Proof. exact (@lem5101879 A B s t h1 _66470). Qed.
Lemma lem5102102 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_66470 : nat) : (term66 A B s t _66470) = (term67 A B s t _66470).
Proof. exact (eq_refl (term66 A B s t _66470)). Qed.
Lemma lem5102104 {B : Type'} (_66471 : B -> Prop) (h1 : term16 B) : term125 B _66471.
Proof. exact (@lem5101905 B h1 _66471). Qed.
Lemma lem5102105 {B : Type'} (_66471 : B -> Prop) : (term125 B _66471) = (term110 B _66471).
Proof. exact (eq_refl (term125 B _66471)). Qed.
Lemma lem5102106 {B : Type'} (_66471 : B -> Prop) (h1 : term16 B) : term110 B _66471.
Proof. exact (EQ_MP (@lem5102105 B _66471) (@lem5102104 B _66471 h1)). Qed.
Lemma lem5102107 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) (h1 : term16 B) : term101 B _66471 _66472.
Proof. exact (@lem5102106 B _66471 h1 _66472). Qed.
Lemma lem5102108 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term101 B _66471 _66472) = (term88 B _66471 _66472).
Proof. exact (eq_refl (term101 B _66471 _66472)). Qed.
Lemma lem5102122 {A : Type'} (_66477 : A -> Prop) (h1 : term16 A) : term147 A _66477.
Proof. exact (@lem5101979 A h1 _66477). Qed.
Lemma lem5102123 {A : Type'} (_66477 : A -> Prop) : (term147 A _66477) = (term144 A _66477).
Proof. exact (eq_refl (term147 A _66477)). Qed.
Lemma lem5102124 {A : Type'} (_66477 : A -> Prop) (h1 : term16 A) : term144 A _66477.
Proof. exact (EQ_MP (@lem5102123 A _66477) (@lem5102122 A _66477 h1)). Qed.
Lemma lem5102125 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) (h1 : term16 A) : term148 A _66477 _66478.
Proof. exact (@lem5102124 A _66477 h1 _66478). Qed.
Lemma lem5102126 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term148 A _66477 _66478) = (term141 A _66477 _66478).
Proof. exact (eq_refl (term148 A _66477 _66478)). Qed.
Lemma lem5102127 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) (h1 : term16 A) : term141 A _66477 _66478.
Proof. exact (EQ_MP (@lem5102126 A _66477 _66478) (@lem5102125 A _66477 _66478 h1)). Qed.
Lemma lem5102140 {A B : Type'} (_66483 : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term62 A B s t _66483.
Proof. exact (@lem5102044 A B s t h1 _66483). Qed.
Lemma lem5102141 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_66483 : nat) : (term62 A B s t _66483) = (term63 A B s t _66483).
Proof. exact (eq_refl (term62 A B s t _66483)). Qed.
Lemma lem5102177 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) (h1 : term16 A) : term88 A _66461 _66462.
Proof. exact (EQ_MP (@lem5102078 A _66461 _66462) (@lem5102077 A _66461 _66462 h1)). Qed.
Lemma lem5102189 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term149 A B s t.
Proof. exact (proj2 (@lem5101698 A B s t h1)). Qed.
Lemma lem5102201 {A B : Type'} (_66470 : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term67 A B s t _66470.
Proof. exact (EQ_MP (@lem5102102 A B s t _66470) (@lem5102101 A B _66470 s t h1)). Qed.
Lemma lem5102203 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5102239 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) (h1 : term16 B) : term150 B _66459 _66460.
Proof. exact (proj2 (@lem5102073 B _66459 _66460 h1)). Qed.
Lemma lem5102249 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) (h1 : term16 B) : term88 B _66471 _66472.
Proof. exact (EQ_MP (@lem5102108 B _66471 _66472) (@lem5102107 B _66471 _66472 h1)). Qed.
Lemma lem5102271 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term149 A B s t.
Proof. exact (proj2 (@lem5101698 A B s t h1)). Qed.
Lemma lem5102277 {A B : Type'} (_66483 : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term63 A B s t _66483.
Proof. exact (EQ_MP (@lem5102141 A B s t _66483) (@lem5102140 A B _66483 s t h1)). Qed.
Lemma lem5102285 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem5102309 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) (h1 : term16 A) : term150 A _66477 _66478.
Proof. exact (proj2 (@lem5102127 A _66477 _66478 h1)). Qed.
Lemma lem5102440 (x : nat) (y : nat) (z : nat) : term151 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem5102448 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5102449 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term152 A s.
Proof. exact (fun h0 : term153 A s => @lem5102448 A s h1). Qed.
Lemma lem5102451 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102452 {A : Type'} (s : A -> Prop) : (term152 A s) = (@FINITE A s).
Proof. exact (@lem5102451 (@FINITE A s)). Qed.
Lemma lem5102453 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem5102452 A s) (@lem5102449 A s h1)). Qed.
Lemma lem5102455 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem5102456 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (@lem5102455 (@CARD A s)). Qed.
Lemma lem5102457 {A : Type'} (s : A -> Prop) : term155 A s.
Proof. exact (fun h0 : term156 A s => @lem5102456 A s). Qed.
Lemma lem5102459 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102460 {A : Type'} (s : A -> Prop) : (term155 A s) = ((@CARD A s) = (@CARD A s)).
Proof. exact (@lem5102459 ((@CARD A s) = (@CARD A s))). Qed.
Lemma lem5102461 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (EQ_MP (@lem5102460 A s) (@lem5102457 A s)). Qed.
Lemma lem5102463 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5102464 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term88 A _66461 _66462) = (term158 A _66461 _66462).
Proof. exact (@lem5102463 (term84 A _66461 _66462) (@HAS_SIZE A _66461 _66462)). Qed.
Lemma lem5102466 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5102467 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term161 A _66461 _66462) = (term162 A _66461 _66462).
Proof. exact (@lem5102466 (term153 A _66461) (term163 A _66461 _66462)). Qed.
Lemma lem5102469 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102470 {A : Type'} (_66461 : A -> Prop) : (term165 A _66461) = (@FINITE A _66461).
Proof. exact (@lem5102469 (@FINITE A _66461)). Qed.
Lemma lem5102471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5102472 {A : Type'} (_66461 : A -> Prop) : (term166 A _66461) = (term167 A _66461).
Proof. exact (MK_COMB (@lem5102471) (@lem5102470 A _66461)). Qed.
Lemma lem5102474 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102475 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term168 A _66461 _66462) = ((@CARD A _66461) = _66462).
Proof. exact (@lem5102474 ((@CARD A _66461) = _66462)). Qed.
Lemma lem5102476 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term162 A _66461 _66462) = (term38 A _66461 _66462).
Proof. exact (MK_COMB (@lem5102472 A _66461) (@lem5102475 A _66461 _66462)). Qed.
Lemma lem5102477 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term161 A _66461 _66462) = (term38 A _66461 _66462).
Proof. exact (TRANS (@lem5102467 A _66461 _66462) (@lem5102476 A _66461 _66462)). Qed.
Lemma lem5102478 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5102479 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term169 A _66461 _66462) = (term170 A _66461 _66462).
Proof. exact (MK_COMB (@lem5102478) (@lem5102477 A _66461 _66462)). Qed.
Lemma lem5102480 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (@HAS_SIZE A _66461 _66462) = (@HAS_SIZE A _66461 _66462).
Proof. exact (eq_refl (@HAS_SIZE A _66461 _66462)). Qed.
Lemma lem5102481 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term158 A _66461 _66462) = (term171 A _66461 _66462).
Proof. exact (MK_COMB (@lem5102479 A _66461 _66462) (@lem5102480 A _66461 _66462)). Qed.
Lemma lem5102482 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) : (term88 A _66461 _66462) = (term171 A _66461 _66462).
Proof. exact (TRANS (@lem5102464 A _66461 _66462) (@lem5102481 A _66461 _66462)). Qed.
Lemma lem5102484 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term172 A s.
Proof. exact (conj (@lem5102453 A s h1) (@lem5102461 A s)). Qed.
Lemma lem5102486 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) (h1 : term16 A) : term171 A _66461 _66462.
Proof. exact (EQ_MP (@lem5102482 A _66461 _66462) (@lem5102177 A _66461 _66462 h1)). Qed.
Lemma lem5102487 {A : Type'} (_66461 : A -> Prop) (_66462 : nat) (h1 : term16 A) : term171 A _66461 _66462.
Proof. exact (@lem5102486 A _66461 _66462 h1). Qed.
Lemma lem5102488 {A : Type'} (s : A -> Prop) (h1 : term16 A) : term173 A s.
Proof. exact (@lem5102487 A s (@CARD A s) h1). Qed.
Lemma lem5102491 {A : Type'} (s : A -> Prop) (h1 : term16 A) (h2 : @FINITE A s) : term174 A s.
Proof. exact (@lem5102488 A s h1 (@lem5102484 A s h2)). Qed.
Lemma lem5102492 {A : Type'} (s : A -> Prop) (h1 : term16 A) (h2 : @FINITE A s) : term175 A s.
Proof. exact (fun h0 : term176 A s => @lem5102491 A s h1 h2). Qed.
Lemma lem5102494 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102495 {A : Type'} (s : A -> Prop) : (term175 A s) = (term174 A s).
Proof. exact (@lem5102494 (term174 A s)). Qed.
Lemma lem5102496 {A : Type'} (s : A -> Prop) (h1 : term16 A) (h2 : @FINITE A s) : term174 A s.
Proof. exact (EQ_MP (@lem5102495 A s) (@lem5102492 A s h1 h2)). Qed.
Lemma lem5102502 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5102503 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : (term67 A B s t _66470) = (term177 A B t s _66470).
Proof. exact (@lem5102502 (@HAS_SIZE B t _66470) (term142 A s _66470)). Qed.
Lemma lem5102509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5102510 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : (term178 A B s t _66470) = (term179 A B t s _66470).
Proof. exact (MK_COMB (@lem5102509) (@lem5102503 A B t s _66470)). Qed.
Lemma lem5102516 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : (term177 A B t s _66470) = (term177 A B t s _66470).
Proof. exact (eq_refl (term177 A B t s _66470)). Qed.
Lemma lem5102517 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : ((term67 A B s t _66470) = (term177 A B t s _66470)) = ((term177 A B t s _66470) = (term177 A B t s _66470)).
Proof. exact (MK_COMB (@lem5102510 A B t s _66470) (@lem5102516 A B t s _66470)). Qed.
Lemma lem5102519 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5102520 (x : Prop) : (x = x) = True.
Proof. exact (@lem5102519 Prop x). Qed.
Lemma lem5102521 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : ((term177 A B t s _66470) = (term177 A B t s _66470)) = True.
Proof. exact (@lem5102520 (term177 A B t s _66470)). Qed.
Lemma lem5102522 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : ((term67 A B s t _66470) = (term177 A B t s _66470)) = True.
Proof. exact (TRANS (@lem5102517 A B t s _66470) (@lem5102521 A B t s _66470)). Qed.
Lemma lem5102523 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : True = ((term67 A B s t _66470) = (term177 A B t s _66470)).
Proof. exact (SYM (@lem5102522 A B t s _66470)). Qed.
Lemma lem5102524 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66470 : nat) : (term67 A B s t _66470) = (term177 A B t s _66470).
Proof. exact (EQ_MP (@lem5102523 A B t s _66470) (@lem0)). Qed.
Lemma lem5102525 {A B : Type'} (_66470 : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term177 A B t s _66470.
Proof. exact (EQ_MP (@lem5102524 A B t s _66470) (@lem5102201 A B _66470 s t h1)). Qed.
Lemma lem5102527 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5102528 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_66470 : nat) : (term177 A B t s _66470) = (term180 A B s t _66470).
Proof. exact (@lem5102527 (term142 A s _66470) (@HAS_SIZE B t _66470)). Qed.
Lemma lem5102530 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102531 {A : Type'} (s : A -> Prop) (_66470 : nat) : (term181 A s _66470) = (@HAS_SIZE A s _66470).
Proof. exact (@lem5102530 (@HAS_SIZE A s _66470)). Qed.
Lemma lem5102532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5102533 {A : Type'} (s : A -> Prop) (_66470 : nat) : (term182 A s _66470) = (term183 A s _66470).
Proof. exact (MK_COMB (@lem5102532) (@lem5102531 A s _66470)). Qed.
Lemma lem5102534 {B : Type'} (t : B -> Prop) (_66470 : nat) : (@HAS_SIZE B t _66470) = (@HAS_SIZE B t _66470).
Proof. exact (eq_refl (@HAS_SIZE B t _66470)). Qed.
Lemma lem5102535 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_66470 : nat) : (term180 A B s t _66470) = (term184 A B s t _66470).
Proof. exact (MK_COMB (@lem5102533 A s _66470) (@lem5102534 B t _66470)). Qed.
Lemma lem5102536 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (_66470 : nat) : (term177 A B t s _66470) = (term184 A B s t _66470).
Proof. exact (TRANS (@lem5102528 A B s t _66470) (@lem5102535 A B s t _66470)). Qed.
Lemma lem5102539 {A B : Type'} (_66470 : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term184 A B s t _66470.
Proof. exact (EQ_MP (@lem5102536 A B s t _66470) (@lem5102525 A B _66470 s t h1)). Qed.
Lemma lem5102540 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term185 A B t s.
Proof. exact (@lem5102539 A B (@CARD A s) s t h1). Qed.
Lemma lem5102543 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : @FINITE A s) (h3 : term15 A B s t) : term186 A B t s.
Proof. exact (@lem5102540 A B s t h3 (@lem5102496 A s h1 h2)). Qed.
Lemma lem5102544 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : @FINITE A s) (h3 : term15 A B s t) : term187 A B t s.
Proof. exact (fun h0 : term188 A B t s => @lem5102543 A B s t h1 h2 h3). Qed.
Lemma lem5102546 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102547 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term187 A B t s) = (term186 A B t s).
Proof. exact (@lem5102546 (term186 A B t s)). Qed.
Lemma lem5102548 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : @FINITE A s) (h3 : term15 A B s t) : term186 A B t s.
Proof. exact (EQ_MP (@lem5102547 A B t s) (@lem5102544 A B s t h1 h2 h3)). Qed.
Lemma lem5102554 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5102555 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term150 B _66459 _66460) = (term189 B _66459 _66460).
Proof. exact (@lem5102554 ((@CARD B _66459) = _66460) (term142 B _66459 _66460)). Qed.
Lemma lem5102563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5102564 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term190 B _66459 _66460) = (term191 B _66459 _66460).
Proof. exact (MK_COMB (@lem5102563) (@lem5102555 B _66459 _66460)). Qed.
Lemma lem5102572 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term189 B _66459 _66460) = (term189 B _66459 _66460).
Proof. exact (eq_refl (term189 B _66459 _66460)). Qed.
Lemma lem5102573 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : ((term150 B _66459 _66460) = (term189 B _66459 _66460)) = ((term189 B _66459 _66460) = (term189 B _66459 _66460)).
Proof. exact (MK_COMB (@lem5102564 B _66459 _66460) (@lem5102572 B _66459 _66460)). Qed.
Lemma lem5102575 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5102576 (x : Prop) : (x = x) = True.
Proof. exact (@lem5102575 Prop x). Qed.
Lemma lem5102577 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : ((term189 B _66459 _66460) = (term189 B _66459 _66460)) = True.
Proof. exact (@lem5102576 (term189 B _66459 _66460)). Qed.
Lemma lem5102578 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : ((term150 B _66459 _66460) = (term189 B _66459 _66460)) = True.
Proof. exact (TRANS (@lem5102573 B _66459 _66460) (@lem5102577 B _66459 _66460)). Qed.
Lemma lem5102579 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : True = ((term150 B _66459 _66460) = (term189 B _66459 _66460)).
Proof. exact (SYM (@lem5102578 B _66459 _66460)). Qed.
Lemma lem5102580 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term150 B _66459 _66460) = (term189 B _66459 _66460).
Proof. exact (EQ_MP (@lem5102579 B _66459 _66460) (@lem0)). Qed.
Lemma lem5102581 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) (h1 : term16 B) : term189 B _66459 _66460.
Proof. exact (EQ_MP (@lem5102580 B _66459 _66460) (@lem5102239 B _66459 _66460 h1)). Qed.
Lemma lem5102583 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5102584 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term189 B _66459 _66460) = (term192 B _66459 _66460).
Proof. exact (@lem5102583 (term142 B _66459 _66460) ((@CARD B _66459) = _66460)). Qed.
Lemma lem5102586 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102587 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term181 B _66459 _66460) = (@HAS_SIZE B _66459 _66460).
Proof. exact (@lem5102586 (@HAS_SIZE B _66459 _66460)). Qed.
Lemma lem5102588 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5102589 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term182 B _66459 _66460) = (term183 B _66459 _66460).
Proof. exact (MK_COMB (@lem5102588) (@lem5102587 B _66459 _66460)). Qed.
Lemma lem5102590 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : ((@CARD B _66459) = _66460) = ((@CARD B _66459) = _66460).
Proof. exact (eq_refl ((@CARD B _66459) = _66460)). Qed.
Lemma lem5102591 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term192 B _66459 _66460) = (term193 B _66459 _66460).
Proof. exact (MK_COMB (@lem5102589 B _66459 _66460) (@lem5102590 B _66459 _66460)). Qed.
Lemma lem5102592 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) : (term189 B _66459 _66460) = (term193 B _66459 _66460).
Proof. exact (TRANS (@lem5102584 B _66459 _66460) (@lem5102591 B _66459 _66460)). Qed.
Lemma lem5102595 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) (h1 : term16 B) : term193 B _66459 _66460.
Proof. exact (EQ_MP (@lem5102592 B _66459 _66460) (@lem5102581 B _66459 _66460 h1)). Qed.
Lemma lem5102596 {B : Type'} (_66459 : B -> Prop) (_66460 : nat) (h1 : term16 B) : term193 B _66459 _66460.
Proof. exact (@lem5102595 B _66459 _66460 h1). Qed.
Lemma lem5102597 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term16 B) : term194 A B t s.
Proof. exact (@lem5102596 B t (@CARD A s) h1). Qed.
Lemma lem5102600 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : (@CARD B t) = (@CARD A s).
Proof. exact (@lem5102597 A B t s h2 (@lem5102548 A B s t h1 h3 h4)). Qed.
Lemma lem5102601 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : term195 A B t s.
Proof. exact (fun h0 : term196 A B t s => @lem5102600 A B s t h1 h2 h3 h4). Qed.
Lemma lem5102603 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102604 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term195 A B t s) = ((@CARD B t) = (@CARD A s)).
Proof. exact (@lem5102603 ((@CARD B t) = (@CARD A s))). Qed.
Lemma lem5102605 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : (@CARD B t) = (@CARD A s).
Proof. exact (EQ_MP (@lem5102604 A B t s) (@lem5102601 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5102607 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem5102608 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (@lem5102607 (@CARD B t)). Qed.
Lemma lem5102609 {B : Type'} (t : B -> Prop) : term155 B t.
Proof. exact (fun h0 : term156 B t => @lem5102608 B t). Qed.
Lemma lem5102611 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102612 {B : Type'} (t : B -> Prop) : (term155 B t) = ((@CARD B t) = (@CARD B t)).
Proof. exact (@lem5102611 ((@CARD B t) = (@CARD B t))). Qed.
Lemma lem5102613 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (EQ_MP (@lem5102612 B t) (@lem5102609 B t)). Qed.
Lemma lem5102631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5102632 (y : nat) (x : nat) (z : nat) : (term197 x y z) = (term198 y x z).
Proof. exact (@lem5102631 (y = z) (term199 x z)). Qed.
Lemma lem5102642 (x : nat) (y : nat) : (term200 x y) = (term200 x y).
Proof. exact (eq_refl (term200 x y)). Qed.
Lemma lem5102643 (y : nat) (x : nat) (z : nat) : (term151 x y z) = (term201 y x z).
Proof. exact (MK_COMB (@lem5102642 x y) (@lem5102632 y x z)). Qed.
Lemma lem5102647 (q : Prop) (p : Prop) (r : Prop) : (term202 p q r) = (term202 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5102648 (y : nat) (x : nat) (z : nat) : (term201 y x z) = (term203 y x z).
Proof. exact (@lem5102647 (y = z) (term199 x y) (term199 x z)). Qed.
Lemma lem5102670 (y : nat) (x : nat) (z : nat) : (term151 x y z) = (term203 y x z).
Proof. exact (TRANS (@lem5102643 y x z) (@lem5102648 y x z)). Qed.
Lemma lem5102671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5102672 (y : nat) (x : nat) (z : nat) : (term204 x y z) = (term205 y x z).
Proof. exact (MK_COMB (@lem5102671) (@lem5102670 y x z)). Qed.
Lemma lem5102694 (y : nat) (x : nat) (z : nat) : (term203 y x z) = (term203 y x z).
Proof. exact (eq_refl (term203 y x z)). Qed.
Lemma lem5102695 (y : nat) (x : nat) (z : nat) : ((term151 x y z) = (term203 y x z)) = ((term203 y x z) = (term203 y x z)).
Proof. exact (MK_COMB (@lem5102672 y x z) (@lem5102694 y x z)). Qed.
Lemma lem5102697 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5102698 (x : Prop) : (x = x) = True.
Proof. exact (@lem5102697 Prop x). Qed.
Lemma lem5102699 (y : nat) (x : nat) (z : nat) : ((term203 y x z) = (term203 y x z)) = True.
Proof. exact (@lem5102698 (term203 y x z)). Qed.
Lemma lem5102700 (y : nat) (x : nat) (z : nat) : ((term151 x y z) = (term203 y x z)) = True.
Proof. exact (TRANS (@lem5102695 y x z) (@lem5102699 y x z)). Qed.
Lemma lem5102701 (y : nat) (x : nat) (z : nat) : True = ((term151 x y z) = (term203 y x z)).
Proof. exact (SYM (@lem5102700 y x z)). Qed.
Lemma lem5102702 (y : nat) (x : nat) (z : nat) : (term151 x y z) = (term203 y x z).
Proof. exact (EQ_MP (@lem5102701 y x z) (@lem0)). Qed.
Lemma lem5102703 (y : nat) (x : nat) (z : nat) : term203 y x z.
Proof. exact (EQ_MP (@lem5102702 y x z) (@lem5102440 x y z)). Qed.
Lemma lem5102705 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5102706 (x : nat) (y : nat) (z : nat) : (term203 y x z) = (term206 x y z).
Proof. exact (@lem5102705 (term207 y x z) (y = z)). Qed.
Lemma lem5102708 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5102709 (y : nat) (x : nat) (z : nat) : (term208 y x z) = (term209 y x z).
Proof. exact (@lem5102708 (term199 x y) (term199 x z)). Qed.
Lemma lem5102711 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102712 (x : nat) (y : nat) : (term210 x y) = (x = y).
Proof. exact (@lem5102711 (x = y)). Qed.
Lemma lem5102713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5102714 (x : nat) (y : nat) : (term211 x y) = (term212 x y).
Proof. exact (MK_COMB (@lem5102713) (@lem5102712 x y)). Qed.
Lemma lem5102716 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102717 (x : nat) (z : nat) : (term210 x z) = (x = z).
Proof. exact (@lem5102716 (x = z)). Qed.
Lemma lem5102718 (y : nat) (x : nat) (z : nat) : (term209 y x z) = (term213 y x z).
Proof. exact (MK_COMB (@lem5102714 x y) (@lem5102717 x z)). Qed.
Lemma lem5102719 (y : nat) (x : nat) (z : nat) : (term208 y x z) = (term213 y x z).
Proof. exact (TRANS (@lem5102709 y x z) (@lem5102718 y x z)). Qed.
Lemma lem5102720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5102721 (y : nat) (x : nat) (z : nat) : (term214 y x z) = (term215 y x z).
Proof. exact (MK_COMB (@lem5102720) (@lem5102719 y x z)). Qed.
Lemma lem5102722 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5102723 (x : nat) (y : nat) (z : nat) : (term206 x y z) = (term216 x y z).
Proof. exact (MK_COMB (@lem5102721 y x z) (@lem5102722 y z)). Qed.
Lemma lem5102724 (x : nat) (y : nat) (z : nat) : (term203 y x z) = (term216 x y z).
Proof. exact (TRANS (@lem5102706 x y z) (@lem5102723 x y z)). Qed.
Lemma lem5102726 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : term217 A B s t.
Proof. exact (conj (@lem5102605 A B s t h1 h2 h3 h4) (@lem5102613 B t)). Qed.
Lemma lem5102728 (x : nat) (y : nat) (z : nat) : term216 x y z.
Proof. exact (EQ_MP (@lem5102724 x y z) (@lem5102703 y x z)). Qed.
Lemma lem5102729 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term218 A B s t.
Proof. exact (@lem5102728 (@CARD B t) (@CARD A s) (@CARD B t)). Qed.
Lemma lem5102732 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : (@CARD A s) = (@CARD B t).
Proof. exact (@lem5102729 A B s t (@lem5102726 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5102733 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : term219 A B s t.
Proof. exact (fun h0 : term149 A B s t => @lem5102732 A B s t h1 h2 h3 h4). Qed.
Lemma lem5102735 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102736 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term219 A B s t) = ((@CARD A s) = (@CARD B t)).
Proof. exact (@lem5102735 ((@CARD A s) = (@CARD B t))). Qed.
Lemma lem5102737 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : (@CARD A s) = (@CARD B t).
Proof. exact (EQ_MP (@lem5102736 A B s t) (@lem5102733 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5102740 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5102742 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term149 A B s t) = (term220 A B s t).
Proof. exact (@lem5102740 ((@CARD A s) = (@CARD B t))). Qed.
Lemma lem5102745 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term220 A B s t.
Proof. exact (EQ_MP (@lem5102742 A B s t) (@lem5102189 A B s t h1)). Qed.
Lemma lem5102748 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : False.
Proof. exact (@lem5102745 A B s t h4 (@lem5102737 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5102749 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : term221.
Proof. exact (fun h0 : ~ False => @lem5102748 A B s t h1 h2 h3 h4). Qed.
Lemma lem5102751 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102752 : term221 = False.
Proof. exact (@lem5102751 False). Qed.
Lemma lem5102753 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5102752) (@lem5102749 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5102880 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem5102881 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : term152 B t.
Proof. exact (fun h0 : term153 B t => @lem5102880 B t h1). Qed.
Lemma lem5102883 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102884 {B : Type'} (t : B -> Prop) : (term152 B t) = (@FINITE B t).
Proof. exact (@lem5102883 (@FINITE B t)). Qed.
Lemma lem5102885 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem5102884 B t) (@lem5102881 B t h1)). Qed.
Lemma lem5102887 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem5102888 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (@lem5102887 (@CARD B t)). Qed.
Lemma lem5102889 {B : Type'} (t : B -> Prop) : term155 B t.
Proof. exact (fun h0 : term156 B t => @lem5102888 B t). Qed.
Lemma lem5102891 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102892 {B : Type'} (t : B -> Prop) : (term155 B t) = ((@CARD B t) = (@CARD B t)).
Proof. exact (@lem5102891 ((@CARD B t) = (@CARD B t))). Qed.
Lemma lem5102893 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (EQ_MP (@lem5102892 B t) (@lem5102889 B t)). Qed.
Lemma lem5102895 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5102896 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term88 B _66471 _66472) = (term158 B _66471 _66472).
Proof. exact (@lem5102895 (term84 B _66471 _66472) (@HAS_SIZE B _66471 _66472)). Qed.
Lemma lem5102898 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5102899 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term161 B _66471 _66472) = (term162 B _66471 _66472).
Proof. exact (@lem5102898 (term153 B _66471) (term163 B _66471 _66472)). Qed.
Lemma lem5102901 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102902 {B : Type'} (_66471 : B -> Prop) : (term165 B _66471) = (@FINITE B _66471).
Proof. exact (@lem5102901 (@FINITE B _66471)). Qed.
Lemma lem5102903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5102904 {B : Type'} (_66471 : B -> Prop) : (term166 B _66471) = (term167 B _66471).
Proof. exact (MK_COMB (@lem5102903) (@lem5102902 B _66471)). Qed.
Lemma lem5102906 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102907 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term168 B _66471 _66472) = ((@CARD B _66471) = _66472).
Proof. exact (@lem5102906 ((@CARD B _66471) = _66472)). Qed.
Lemma lem5102908 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term162 B _66471 _66472) = (term38 B _66471 _66472).
Proof. exact (MK_COMB (@lem5102904 B _66471) (@lem5102907 B _66471 _66472)). Qed.
Lemma lem5102909 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term161 B _66471 _66472) = (term38 B _66471 _66472).
Proof. exact (TRANS (@lem5102899 B _66471 _66472) (@lem5102908 B _66471 _66472)). Qed.
Lemma lem5102910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5102911 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term169 B _66471 _66472) = (term170 B _66471 _66472).
Proof. exact (MK_COMB (@lem5102910) (@lem5102909 B _66471 _66472)). Qed.
Lemma lem5102912 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (@HAS_SIZE B _66471 _66472) = (@HAS_SIZE B _66471 _66472).
Proof. exact (eq_refl (@HAS_SIZE B _66471 _66472)). Qed.
Lemma lem5102913 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term158 B _66471 _66472) = (term171 B _66471 _66472).
Proof. exact (MK_COMB (@lem5102911 B _66471 _66472) (@lem5102912 B _66471 _66472)). Qed.
Lemma lem5102914 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) : (term88 B _66471 _66472) = (term171 B _66471 _66472).
Proof. exact (TRANS (@lem5102896 B _66471 _66472) (@lem5102913 B _66471 _66472)). Qed.
Lemma lem5102916 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : term172 B t.
Proof. exact (conj (@lem5102885 B t h1) (@lem5102893 B t)). Qed.
Lemma lem5102918 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) (h1 : term16 B) : term171 B _66471 _66472.
Proof. exact (EQ_MP (@lem5102914 B _66471 _66472) (@lem5102249 B _66471 _66472 h1)). Qed.
Lemma lem5102919 {B : Type'} (_66471 : B -> Prop) (_66472 : nat) (h1 : term16 B) : term171 B _66471 _66472.
Proof. exact (@lem5102918 B _66471 _66472 h1). Qed.
Lemma lem5102920 {B : Type'} (t : B -> Prop) (h1 : term16 B) : term173 B t.
Proof. exact (@lem5102919 B t (@CARD B t) h1). Qed.
Lemma lem5102923 {B : Type'} (t : B -> Prop) (h1 : term16 B) (h2 : @FINITE B t) : term174 B t.
Proof. exact (@lem5102920 B t h1 (@lem5102916 B t h2)). Qed.
Lemma lem5102924 {B : Type'} (t : B -> Prop) (h1 : term16 B) (h2 : @FINITE B t) : term175 B t.
Proof. exact (fun h0 : term176 B t => @lem5102923 B t h1 h2). Qed.
Lemma lem5102926 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102927 {B : Type'} (t : B -> Prop) : (term175 B t) = (term174 B t).
Proof. exact (@lem5102926 (term174 B t)). Qed.
Lemma lem5102928 {B : Type'} (t : B -> Prop) (h1 : term16 B) (h2 : @FINITE B t) : term174 B t.
Proof. exact (EQ_MP (@lem5102927 B t) (@lem5102924 B t h1 h2)). Qed.
Lemma lem5102930 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5102931 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66483 : nat) : (term63 A B s t _66483) = (term222 A B t s _66483).
Proof. exact (@lem5102930 (term142 B t _66483) (@HAS_SIZE A s _66483)). Qed.
Lemma lem5102933 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102934 {B : Type'} (t : B -> Prop) (_66483 : nat) : (term181 B t _66483) = (@HAS_SIZE B t _66483).
Proof. exact (@lem5102933 (@HAS_SIZE B t _66483)). Qed.
Lemma lem5102935 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5102936 {B : Type'} (t : B -> Prop) (_66483 : nat) : (term182 B t _66483) = (term183 B t _66483).
Proof. exact (MK_COMB (@lem5102935) (@lem5102934 B t _66483)). Qed.
Lemma lem5102937 {A : Type'} (s : A -> Prop) (_66483 : nat) : (@HAS_SIZE A s _66483) = (@HAS_SIZE A s _66483).
Proof. exact (eq_refl (@HAS_SIZE A s _66483)). Qed.
Lemma lem5102938 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66483 : nat) : (term222 A B t s _66483) = (term223 A B t s _66483).
Proof. exact (MK_COMB (@lem5102936 B t _66483) (@lem5102937 A s _66483)). Qed.
Lemma lem5102939 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (_66483 : nat) : (term63 A B s t _66483) = (term223 A B t s _66483).
Proof. exact (TRANS (@lem5102931 A B t s _66483) (@lem5102938 A B t s _66483)). Qed.
Lemma lem5102942 {A B : Type'} (_66483 : nat) (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term223 A B t s _66483.
Proof. exact (EQ_MP (@lem5102939 A B t s _66483) (@lem5102277 A B _66483 s t h1)). Qed.
Lemma lem5102943 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term224 A B s t.
Proof. exact (@lem5102942 A B (@CARD B t) s t h1). Qed.
Lemma lem5102946 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 B) (h2 : @FINITE B t) (h3 : term15 A B s t) : term225 A B s t.
Proof. exact (@lem5102943 A B s t h3 (@lem5102928 B t h1 h2)). Qed.
Lemma lem5102947 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 B) (h2 : @FINITE B t) (h3 : term15 A B s t) : term226 A B s t.
Proof. exact (fun h0 : term227 A B s t => @lem5102946 A B s t h1 h2 h3). Qed.
Lemma lem5102949 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5102950 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term226 A B s t) = (term225 A B s t).
Proof. exact (@lem5102949 (term225 A B s t)). Qed.
Lemma lem5102951 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 B) (h2 : @FINITE B t) (h3 : term15 A B s t) : term225 A B s t.
Proof. exact (EQ_MP (@lem5102950 A B s t) (@lem5102947 A B s t h1 h2 h3)). Qed.
Lemma lem5102957 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5102958 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term150 A _66477 _66478) = (term189 A _66477 _66478).
Proof. exact (@lem5102957 ((@CARD A _66477) = _66478) (term142 A _66477 _66478)). Qed.
Lemma lem5102966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5102967 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term190 A _66477 _66478) = (term191 A _66477 _66478).
Proof. exact (MK_COMB (@lem5102966) (@lem5102958 A _66477 _66478)). Qed.
Lemma lem5102975 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term189 A _66477 _66478) = (term189 A _66477 _66478).
Proof. exact (eq_refl (term189 A _66477 _66478)). Qed.
Lemma lem5102976 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : ((term150 A _66477 _66478) = (term189 A _66477 _66478)) = ((term189 A _66477 _66478) = (term189 A _66477 _66478)).
Proof. exact (MK_COMB (@lem5102967 A _66477 _66478) (@lem5102975 A _66477 _66478)). Qed.
Lemma lem5102978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5102979 (x : Prop) : (x = x) = True.
Proof. exact (@lem5102978 Prop x). Qed.
Lemma lem5102980 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : ((term189 A _66477 _66478) = (term189 A _66477 _66478)) = True.
Proof. exact (@lem5102979 (term189 A _66477 _66478)). Qed.
Lemma lem5102981 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : ((term150 A _66477 _66478) = (term189 A _66477 _66478)) = True.
Proof. exact (TRANS (@lem5102976 A _66477 _66478) (@lem5102980 A _66477 _66478)). Qed.
Lemma lem5102982 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : True = ((term150 A _66477 _66478) = (term189 A _66477 _66478)).
Proof. exact (SYM (@lem5102981 A _66477 _66478)). Qed.
Lemma lem5102983 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term150 A _66477 _66478) = (term189 A _66477 _66478).
Proof. exact (EQ_MP (@lem5102982 A _66477 _66478) (@lem0)). Qed.
Lemma lem5102984 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) (h1 : term16 A) : term189 A _66477 _66478.
Proof. exact (EQ_MP (@lem5102983 A _66477 _66478) (@lem5102309 A _66477 _66478 h1)). Qed.
Lemma lem5102986 (b : Prop) (a : Prop) : (a \/ b) = (term157 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5102987 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term189 A _66477 _66478) = (term192 A _66477 _66478).
Proof. exact (@lem5102986 (term142 A _66477 _66478) ((@CARD A _66477) = _66478)). Qed.
Lemma lem5102989 (a : Prop) : (term164 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5102990 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term181 A _66477 _66478) = (@HAS_SIZE A _66477 _66478).
Proof. exact (@lem5102989 (@HAS_SIZE A _66477 _66478)). Qed.
Lemma lem5102991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5102992 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term182 A _66477 _66478) = (term183 A _66477 _66478).
Proof. exact (MK_COMB (@lem5102991) (@lem5102990 A _66477 _66478)). Qed.
Lemma lem5102993 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : ((@CARD A _66477) = _66478) = ((@CARD A _66477) = _66478).
Proof. exact (eq_refl ((@CARD A _66477) = _66478)). Qed.
Lemma lem5102994 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term192 A _66477 _66478) = (term193 A _66477 _66478).
Proof. exact (MK_COMB (@lem5102992 A _66477 _66478) (@lem5102993 A _66477 _66478)). Qed.
Lemma lem5102995 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) : (term189 A _66477 _66478) = (term193 A _66477 _66478).
Proof. exact (TRANS (@lem5102987 A _66477 _66478) (@lem5102994 A _66477 _66478)). Qed.
Lemma lem5102998 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) (h1 : term16 A) : term193 A _66477 _66478.
Proof. exact (EQ_MP (@lem5102995 A _66477 _66478) (@lem5102984 A _66477 _66478 h1)). Qed.
Lemma lem5102999 {A : Type'} (_66477 : A -> Prop) (_66478 : nat) (h1 : term16 A) : term193 A _66477 _66478.
Proof. exact (@lem5102998 A _66477 _66478 h1). Qed.
Lemma lem5103000 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) : term228 A B s t.
Proof. exact (@lem5102999 A s (@CARD B t) h1). Qed.
Lemma lem5103003 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : (@CARD A s) = (@CARD B t).
Proof. exact (@lem5103000 A B s t h1 (@lem5102951 A B s t h2 h3 h4)). Qed.
Lemma lem5103004 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : term219 A B s t.
Proof. exact (fun h0 : term149 A B s t => @lem5103003 A B s t h1 h2 h3 h4). Qed.
Lemma lem5103006 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5103007 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term219 A B s t) = ((@CARD A s) = (@CARD B t)).
Proof. exact (@lem5103006 ((@CARD A s) = (@CARD B t))). Qed.
Lemma lem5103008 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : (@CARD A s) = (@CARD B t).
Proof. exact (EQ_MP (@lem5103007 A B s t) (@lem5103004 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5103011 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5103013 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term149 A B s t) = (term220 A B s t).
Proof. exact (@lem5103011 ((@CARD A s) = (@CARD B t))). Qed.
Lemma lem5103016 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term220 A B s t.
Proof. exact (EQ_MP (@lem5103013 A B s t) (@lem5102271 A B s t h1)). Qed.
Lemma lem5103019 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : False.
Proof. exact (@lem5103016 A B s t h4 (@lem5103008 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5103020 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : term221.
Proof. exact (fun h0 : ~ False => @lem5103019 A B s t h1 h2 h3 h4). Qed.
Lemma lem5103022 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5103023 : term221 = False.
Proof. exact (@lem5103022 False). Qed.
Lemma lem5103024 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103023) (@lem5103020 A B s t h1 h2 h3 h4)). Qed.
Lemma lem5103025 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h5 : @FINITE B t => @lem5103024 A B s t h1 h2 h3 h4) (fun h5 : False => @lem5102285 B t h3)). Qed.
Lemma lem5103026 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103025 A B s t h1 h2 h3 h4) (@lem5102285 B t h3)). Qed.
Lemma lem5103027 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem5102753 A B s t h1 h2 h3 h4) (fun h5 : False => @lem5102203 A s h3)). Qed.
Lemma lem5103028 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103027 A B s t h1 h2 h3 h4) (@lem5102203 A s h3)). Qed.
Lemma lem5103029 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h5 : @FINITE B t => @lem5103026 A B s t h1 h2 h3 h4) (fun h5 : False => @lem5102061 B t h3)). Qed.
Lemma lem5103030 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103029 A B s t h1 h2 h3 h4) (@lem5102061 B t h3)). Qed.
Lemma lem5103031 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem5103028 A B s t h1 h2 h3 h4) (fun h5 : False => @lem5101883 A s h3)). Qed.
Lemma lem5103032 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103031 A B s t h1 h2 h3 h4) (@lem5101883 A s h3)). Qed.
Lemma lem5103033 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : (@FINITE B t) = False.
Proof. exact (prop_ext (fun h5 : @FINITE B t => @lem5103030 A B s t h1 h2 h3 h4) (fun h5 : False => @lem5102061 B t h3)). Qed.
Lemma lem5103034 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE B t) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103033 A B s t h1 h2 h3 h4) (@lem5102061 B t h3)). Qed.
Lemma lem5103035 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem5103032 A B s t h1 h2 h3 h4) (fun h5 : False => @lem5101883 A s h3)). Qed.
Lemma lem5103036 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : @FINITE A s) (h4 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103035 A B s t h1 h2 h3 h4) (@lem5101883 A s h3)). Qed.
Lemma lem5103037 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B s t) : False.
Proof. exact (or_elim (@lem5101701 A B s t h3) (fun h0 : @FINITE A s => @lem5103036 A B s t h1 h2 h0 h3) (fun h0 : @FINITE B t => @lem5103034 A B s t h1 h2 h0 h3)). Qed.
Lemma lem5103038 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term15 A B s t) : term21 B.
Proof. exact (fun h0 : term16 B => @lem5103037 A B s t h1 h0 h2). Qed.
Lemma lem5103039 {B : Type'} : (term21 B) = (term22 B).
Proof. exact (@lem69 (term16 B)). Qed.
Lemma lem5103040 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term16 A) (h2 : term15 A B s t) : term22 B.
Proof. exact (EQ_MP (@lem5103039 B) (@lem5103038 A B s t h1 h2)). Qed.
Lemma lem5103041 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term25 A B.
Proof. exact (fun h0 : term16 A => @lem5103040 A B s t h0 h1). Qed.
Lemma lem5103042 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term27 _100044 A B.
Proof. exact (fun h0 : term16 _100044 => @lem5103041 A B s t h1). Qed.
Lemma lem5103043 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : term29 _100044 A B s t.
Proof. exact (fun h0 : term15 A B s t => @lem5103042 _100044 A B s t h0). Qed.
Lemma lem5103048 {_100044 A B : Type'} (t : B -> Prop) : term33 _100044 A B t.
Proof. exact (fun s : A -> Prop => @lem5103043 _100044 A B s t). Qed.
Lemma lem5103053 {_100044 A B : Type'} : term37 _100044 A B.
Proof. exact (fun t : B -> Prop => @lem5103048 _100044 A B t). Qed.
Lemma lem5103054 {_100044 A B : Type'} : term36 _100044 A B.
Proof. exact (EQ_MP (@lem5100373 _100044 A B) (@lem5103053 _100044 A B)). Qed.
Lemma lem5103055 {_100044 A B : Type'} (t : B -> Prop) : term229 _100044 A B t.
Proof. exact (@lem5103054 _100044 A B t). Qed.
Lemma lem5103056 {_100044 A B : Type'} (t : B -> Prop) : (term229 _100044 A B t) = (term32 _100044 A B t).
Proof. exact (eq_refl (term229 _100044 A B t)). Qed.
Lemma lem5103057 {_100044 A B : Type'} (t : B -> Prop) : term32 _100044 A B t.
Proof. exact (EQ_MP (@lem5103056 _100044 A B t) (@lem5103055 _100044 A B t)). Qed.
Lemma lem5103058 {_100044 A B : Type'} (t : B -> Prop) (s : A -> Prop) : term230 _100044 A B t s.
Proof. exact (@lem5103057 _100044 A B t s). Qed.
Lemma lem5103059 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term230 _100044 A B t s) = (term17 _100044 A B s t).
Proof. exact (eq_refl (term230 _100044 A B t s)). Qed.
Lemma lem5103060 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : term17 _100044 A B s t.
Proof. exact (EQ_MP (@lem5103059 _100044 A B s t) (@lem5103058 _100044 A B t s)). Qed.
Lemma lem5103062 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) : term17 _100044 A B s t.
Proof. exact (@lem5100126 _100044 A B s t (@lem5103060 _100044 A B s t)). Qed.
Lemma lem5103063 {_100044 A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term26 _100044 A B.
Proof. exact (@lem5103062 _100044 A B s t (@lem5100104 A B s t h1)). Qed.
Lemma lem5103064 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term24 A B.
Proof. exact (@lem5103063 Prop A B s t h1 (@lem3863773 Prop)). Qed.
Lemma lem5103065 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : term21 B.
Proof. exact (@lem5103064 A B s t h1 (@lem5100105 A)). Qed.
Lemma lem5103066 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : False.
Proof. exact (@lem5103065 A B s t h1 (@lem5100106 B)). Qed.
Lemma lem5103067 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : (term15 A B s t) = False.
Proof. exact (prop_ext (fun h2 : term15 A B s t => @lem5103066 A B s t h1) (fun h2 : False => @lem5100104 A B s t h1)). Qed.
Lemma lem5103068 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term15 A B s t) : False.
Proof. exact (EQ_MP (@lem5103067 A B s t h1) (@lem5100104 A B s t h1)). Qed.
Lemma lem5103069 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term14 A B s t.
Proof. exact (fun h0 : term15 A B s t => @lem5103068 A B s t h0). Qed.
Lemma lem5103070 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term13 A B s t.
Proof. exact (EQ_MP (@lem5100103 A B s t) (@lem5103069 A B s t)). Qed.
Lemma lem5103071 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term8 A B t s f g) : term9 A B t s f g.
Proof. exact (proj2 (@lem5100093 A B t s f g h1)). Qed.
Lemma lem5103072 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term8 A B t s f g) : term11 A B s t.
Proof. exact (proj1 (@lem5100093 A B t s f g h1)). Qed.
Lemma lem5103073 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term9 A B t s f g) : term42 A B s t.
Proof. exact (@lem5103070 A B s t (@lem5100098 A B t s f g h1)). Qed.
Lemma lem5103074 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (h1 : term9 A B t s f g) (h2 : term11 A B s t) : (@CARD A s) = (@CARD B t).
Proof. exact (@lem5103073 A B t s f g h1 (@lem5100099 A B s t h2)). Qed.
Lemma lem5103075 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (h1 : term8 A B t s f g) (h2 : term11 A B s t) : (term9 A B t s f g) = ((@CARD A s) = (@CARD B t)).
Proof. exact (prop_ext (fun h3 : term9 A B t s f g => @lem5103074 A B f g s t h3 h2) (fun h3 : (@CARD A s) = (@CARD B t) => @lem5103071 A B t s f g h1)). Qed.
Lemma lem5103076 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (h1 : term8 A B t s f g) (h2 : term11 A B s t) : (@CARD A s) = (@CARD B t).
Proof. exact (EQ_MP (@lem5103075 A B f g s t h1 h2) (@lem5103071 A B t s f g h1)). Qed.
Lemma lem5103077 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term8 A B t s f g) : (term11 A B s t) = ((@CARD A s) = (@CARD B t)).
Proof. exact (prop_ext (fun h2 : term11 A B s t => @lem5103076 A B f g s t h1 h2) (fun h2 : (@CARD A s) = (@CARD B t) => @lem5103072 A B t s f g h1)). Qed.
Lemma lem5103078 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term8 A B t s f g) : (@CARD A s) = (@CARD B t).
Proof. exact (EQ_MP (@lem5103077 A B t s f g h1) (@lem5103072 A B t s f g h1)). Qed.
Lemma lem5103079 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) : term231 A B f g s t.
Proof. exact (fun h0 : term8 A B t s f g => @lem5103078 A B t s f g h0). Qed.
Lemma lem5103084 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term232 A B f s t.
Proof. exact (fun g : B -> A => @lem5103079 A B f g s t). Qed.
Lemma lem5103089 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term233 A B s t.
Proof. exact (fun f : A -> B => @lem5103084 A B f s t). Qed.
Lemma lem5103094 {A B : Type'} (s : A -> Prop) : term234 A B s.
Proof. exact (fun t : B -> Prop => @lem5103089 A B s t). Qed.
Lemma lem5103099 {A B : Type'} : term235 A B.
Proof. exact (fun s : A -> Prop => @lem5103094 A B s). Qed.
