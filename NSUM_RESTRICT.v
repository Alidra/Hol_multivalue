Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_RESTRICT_term_abbrevs.
Require Import NSUM_EQ_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem6970186 {_127166 : Type'} (h1 : term0 _127166) : term0 _127166.
Proof. exact (h1). Qed.
Lemma lem6970187 {_127166 : Type'} (f : _127166 -> nat) (h1 : term0 _127166) : term1 _127166 f.
Proof. exact (@lem6970186 _127166 h1 f). Qed.
Lemma lem6970188 {_127166 : Type'} (f : _127166 -> nat) : (term1 _127166 f) = (term2 _127166 f).
Proof. exact (eq_refl (term1 _127166 f)). Qed.
Lemma lem6970189 {_127166 : Type'} (f : _127166 -> nat) (h1 : term0 _127166) : term2 _127166 f.
Proof. exact (EQ_MP (@lem6970188 _127166 f) (@lem6970187 _127166 f h1)). Qed.
Lemma lem6970190 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term0 _127166) : term3 _127166 f g.
Proof. exact (@lem6970189 _127166 f h1 g). Qed.
Lemma lem6970191 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) : (term3 _127166 f g) = (term4 _127166 f g).
Proof. exact (eq_refl (term3 _127166 f g)). Qed.
Lemma lem6970192 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term0 _127166) : term4 _127166 f g.
Proof. exact (EQ_MP (@lem6970191 _127166 f g) (@lem6970190 _127166 f g h1)). Qed.
Lemma lem6970193 {_127166 : Type'} (f : _127166 -> nat) (g : _127166 -> nat) (s : _127166 -> Prop) (h1 : term0 _127166) : term5 _127166 f g s.
Proof. exact (@lem6970192 _127166 f g h1 s). Qed.
Lemma lem6970194 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term5 _127166 f g s) = (term6 _127166 f s g).
Proof. exact (eq_refl (term5 _127166 f g s)). Qed.
Lemma lem6970195 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term0 _127166) : term6 _127166 f s g.
Proof. exact (EQ_MP (@lem6970194 _127166 f s g) (@lem6970193 _127166 f g s h1)). Qed.
Lemma lem6970196 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) : term7 _127166 s f g.
Proof. exact (h1). Qed.
Lemma lem6970197 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) (h2 : term0 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6970195 _127166 f s g h2 (@lem6970196 _127166 s f g h1)). Qed.
Lemma lem6970198 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) : term8 _127166 f s g.
Proof. exact (fun h0 : term0 _127166 => @lem6970197 _127166 s f g h1 h0). Qed.
Lemma lem6970199 {_127166 : Type'} (h1 : term0 _127166) : term0 _127166.
Proof. exact (h1). Qed.
Lemma lem6970200 {_127166 : Type'} (s : _127166 -> Prop) (f : _127166 -> nat) (g : _127166 -> nat) (h1 : term7 _127166 s f g) (h2 : term0 _127166) : (@nsum _127166 s f) = (@nsum _127166 s g).
Proof. exact (@lem6970198 _127166 s f g h1 (@lem6970199 _127166 h2)). Qed.
Lemma lem6970201 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) (h1 : term0 _127166) : term6 _127166 f s g.
Proof. exact (fun h0 : term7 _127166 s f g => @lem6970200 _127166 s f g h0 h1). Qed.
Lemma lem6970202 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (h1 : term0 _127166) : term9 _127166 f s.
Proof. exact (fun g : _127166 -> nat => @lem6970201 _127166 f s g h1). Qed.
Lemma lem6970203 {_127166 : Type'} (f : _127166 -> nat) (h1 : term0 _127166) : term10 _127166 f.
Proof. exact (fun s : _127166 -> Prop => @lem6970202 _127166 f s h1). Qed.
Lemma lem6970204 {_127166 : Type'} (h1 : term0 _127166) : term11 _127166.
Proof. exact (fun f : _127166 -> nat => @lem6970203 _127166 f h1). Qed.
Lemma lem6970205 {_127166 : Type'} : term12 _127166.
Proof. exact (fun h0 : term0 _127166 => @lem6970204 _127166 h0). Qed.
Lemma lem6970206 {_127166 : Type'} : term11 _127166.
Proof. exact (@lem6970205 _127166 (@lem6938831 _127166)). Qed.
Lemma lem6970207 {_127166 : Type'} (f : _127166 -> nat) : term13 _127166 f.
Proof. exact (@lem6970206 _127166 f). Qed.
Lemma lem6970208 {_127166 : Type'} (f : _127166 -> nat) : (term13 _127166 f) = (term10 _127166 f).
Proof. exact (eq_refl (term13 _127166 f)). Qed.
Lemma lem6970209 {_127166 : Type'} (f : _127166 -> nat) : term10 _127166 f.
Proof. exact (EQ_MP (@lem6970208 _127166 f) (@lem6970207 _127166 f)). Qed.
Lemma lem6970210 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term14 _127166 f s.
Proof. exact (@lem6970209 _127166 f s). Qed.
Lemma lem6970211 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : (term14 _127166 f s) = (term9 _127166 f s).
Proof. exact (eq_refl (term14 _127166 f s)). Qed.
Lemma lem6970212 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) : term9 _127166 f s.
Proof. exact (EQ_MP (@lem6970211 _127166 f s) (@lem6970210 _127166 f s)). Qed.
Lemma lem6970213 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term15 _127166 f s g.
Proof. exact (@lem6970212 _127166 f s g). Qed.
Lemma lem6970214 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : (term15 _127166 f s g) = (term6 _127166 f s g).
Proof. exact (eq_refl (term15 _127166 f s g)). Qed.
Lemma lem6970218 {_127166 : Type'} (f : _127166 -> nat) (s : _127166 -> Prop) (g : _127166 -> nat) : term6 _127166 f s g.
Proof. exact (EQ_MP (@lem6970214 _127166 f s g) (@lem6970213 _127166 f s g)). Qed.
Lemma lem6970219 {_127848 : Type'} (f : _127848 -> nat) (s : _127848 -> Prop) (g : _127848 -> nat) : term6 _127848 f s g.
Proof. exact (@lem6970218 _127848 f s g). Qed.
Lemma lem6970220 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : term16 _127848 s f.
Proof. exact (@lem6970219 _127848 (term17 _127848 s f) s f). Qed.
Lemma lem6970230 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term18 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6970231 (p : Prop) (q : Prop) (p' : Prop) : term19 p q p'.
Proof. exact (fun q' : Prop => @lem6970230 p q p' q'). Qed.
Lemma lem6970232 (p : Prop) (q : Prop) : term20 p q.
Proof. exact (fun p' : Prop => @lem6970231 p q p'). Qed.
Lemma lem6970233 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : term21 _127848 s f x.
Proof. exact (@lem6970232 (@IN _127848 x s) ((term22 _127848 s f x) = (f x))). Qed.
Lemma lem6970234 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (p' : Prop) : term23 _127848 s f x p'.
Proof. exact (@lem6970233 _127848 s f x p'). Qed.
Lemma lem6970235 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (p' : Prop) : (term23 _127848 s f x p') = (term24 _127848 s f x p').
Proof. exact (eq_refl (term23 _127848 s f x p')). Qed.
Lemma lem6970236 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (p' : Prop) : term24 _127848 s f x p'.
Proof. exact (EQ_MP (@lem6970235 _127848 s f x p') (@lem6970234 _127848 s f x p')). Qed.
Lemma lem6970237 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (p' : Prop) (q' : Prop) : term25 _127848 s f x p' q'.
Proof. exact (@lem6970236 _127848 s f x p' q'). Qed.
Lemma lem6970238 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (p' : Prop) (q' : Prop) : (term25 _127848 s f x p' q') = (term26 _127848 s f x p' q').
Proof. exact (eq_refl (term25 _127848 s f x p' q')). Qed.
Lemma lem6970239 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (p' : Prop) (q' : Prop) : term26 _127848 s f x p' q'.
Proof. exact (EQ_MP (@lem6970238 _127848 s f x p' q') (@lem6970237 _127848 s f x p' q')). Qed.
Lemma lem6970240 {_127848 : Type'} (x : _127848) (s : _127848 -> Prop) : (@IN _127848 x s) = (@IN _127848 x s).
Proof. exact (eq_refl (@IN _127848 x s)). Qed.
Lemma lem6970241 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (q' : Prop) : term27 _127848 f x s q'.
Proof. exact (@lem6970239 _127848 s f x (@IN _127848 x s) q'). Qed.
Lemma lem6970242 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (q' : Prop) : term28 _127848 f x s q'.
Proof. exact (@lem6970241 _127848 f x s q' (@lem6970240 _127848 x s)). Qed.
Lemma lem6970243 {_127848 : Type'} (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : @IN _127848 x s.
Proof. exact (h1). Qed.
Lemma lem6970244 {_127848 : Type'} (x : _127848) (s : _127848 -> Prop) : (@IN _127848 x s) = ((@IN _127848 x s) = True).
Proof. exact (@lem7 (@IN _127848 x s)). Qed.
Lemma lem6970249 {A B : Type'} (f : A -> B) (y : A) : (term29 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6970250 {_127848 : Type'} (f : _127848 -> nat) (y : _127848) : (term30 _127848 f y) = (f y).
Proof. exact (@lem6970249 _127848 nat f y). Qed.
Lemma lem6970251 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : (term31 _127848 s f x) = (term22 _127848 s f x).
Proof. exact (@lem6970250 _127848 (term17 _127848 s f) x). Qed.
Lemma lem6970252 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : (term22 _127848 s f x) = (term32 _127848 s f x).
Proof. exact (eq_refl (term22 _127848 s f x)). Qed.
Lemma lem6970253 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : (term33 _127848 s f) = (term17 _127848 s f).
Proof. exact (fun_ext (fun x : _127848 => @lem6970252 _127848 s f x)). Qed.
Lemma lem6970254 {_127848 : Type'} (x : _127848) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6970255 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : (term31 _127848 s f x) = (term22 _127848 s f x).
Proof. exact (MK_COMB (@lem6970253 _127848 s f) (@lem6970254 _127848 x)). Qed.
Lemma lem6970256 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6970257 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : (term34 _127848 s f x) = (term35 _127848 s f x).
Proof. exact (MK_COMB (@lem6970256) (@lem6970255 _127848 s f x)). Qed.
Lemma lem6970258 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : (term22 _127848 s f x) = (term32 _127848 s f x).
Proof. exact (eq_refl (term22 _127848 s f x)). Qed.
Lemma lem6970259 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : ((term31 _127848 s f x) = (term22 _127848 s f x)) = ((term22 _127848 s f x) = (term32 _127848 s f x)).
Proof. exact (MK_COMB (@lem6970257 _127848 s f x) (@lem6970258 _127848 s f x)). Qed.
Lemma lem6970260 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : (term22 _127848 s f x) = (term32 _127848 s f x).
Proof. exact (EQ_MP (@lem6970259 _127848 s f x) (@lem6970251 _127848 s f x)). Qed.
Lemma lem6970262 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term36 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6970263 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term37 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6970262 _2963 g t e g' t' e'). Qed.
Lemma lem6970264 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term38 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6970263 _2963 g t e g' t'). Qed.
Lemma lem6970265 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term39 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6970264 _2963 g t e g'). Qed.
Lemma lem6970266 (g : Prop) (t : nat) (e : nat) : term40 g t e.
Proof. exact (@lem6970265 nat g t e). Qed.
Lemma lem6970267 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : term41 _127848 s f x.
Proof. exact (@lem6970266 (@IN _127848 x s) (f x) (NUMERAL 0)). Qed.
Lemma lem6970268 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) : term42 _127848 s f x g'.
Proof. exact (@lem6970267 _127848 s f x g'). Qed.
Lemma lem6970269 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) : (term42 _127848 s f x g') = (term43 _127848 s f x g').
Proof. exact (eq_refl (term42 _127848 s f x g')). Qed.
Lemma lem6970270 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) : term43 _127848 s f x g'.
Proof. exact (EQ_MP (@lem6970269 _127848 s f x g') (@lem6970268 _127848 s f x g')). Qed.
Lemma lem6970271 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) (t' : nat) : term44 _127848 s f x g' t'.
Proof. exact (@lem6970270 _127848 s f x g' t'). Qed.
Lemma lem6970272 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) (t' : nat) : (term44 _127848 s f x g' t') = (term45 _127848 s f x g' t').
Proof. exact (eq_refl (term44 _127848 s f x g' t')). Qed.
Lemma lem6970273 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) (t' : nat) : term45 _127848 s f x g' t'.
Proof. exact (EQ_MP (@lem6970272 _127848 s f x g' t') (@lem6970271 _127848 s f x g' t')). Qed.
Lemma lem6970274 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) (t' : nat) (e' : nat) : term46 _127848 s f x g' t' e'.
Proof. exact (@lem6970273 _127848 s f x g' t' e'). Qed.
Lemma lem6970275 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) (t' : nat) (e' : nat) : (term46 _127848 s f x g' t' e') = (term47 _127848 s f x g' t' e').
Proof. exact (eq_refl (term46 _127848 s f x g' t' e')). Qed.
Lemma lem6970276 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (g' : Prop) (t' : nat) (e' : nat) : term47 _127848 s f x g' t' e'.
Proof. exact (EQ_MP (@lem6970275 _127848 s f x g' t' e') (@lem6970274 _127848 s f x g' t' e')). Qed.
Lemma lem6970278 {_127848 : Type'} (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : (@IN _127848 x s) = True.
Proof. exact (EQ_MP (@lem6970244 _127848 x s) (@lem6970243 _127848 x s h1)). Qed.
Lemma lem6970279 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) (t' : nat) (e' : nat) : term48 _127848 s f x t' e'.
Proof. exact (@lem6970276 _127848 s f x True t' e'). Qed.
Lemma lem6970280 {_127848 : Type'} (f : _127848 -> nat) (t' : nat) (e' : nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : term49 _127848 s f x t' e'.
Proof. exact (@lem6970279 _127848 s f x t' e' (@lem6970278 _127848 x s h1)). Qed.
Lemma lem6970286 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6970287 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) : term50 _127848 f x.
Proof. exact (fun h0 : True => @lem6970286 _127848 f x). Qed.
Lemma lem6970288 {_127848 : Type'} (f : _127848 -> nat) (e' : nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : term51 _127848 s f x e'.
Proof. exact (@lem6970280 _127848 f (f x) e' x s h1). Qed.
Lemma lem6970289 {_127848 : Type'} (f : _127848 -> nat) (e' : nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : term52 _127848 s f x e'.
Proof. exact (@lem6970288 _127848 f e' x s h1 (@lem6970287 _127848 f x)). Qed.
Lemma lem6970293 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem6970294 : term53.
Proof. exact (fun h0 : ~ True => @lem6970293). Qed.
Lemma lem6970295 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : term54 _127848 s f x.
Proof. exact (@lem6970289 _127848 f (NUMERAL 0) x s h1). Qed.
Lemma lem6970296 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : (term32 _127848 s f x) = (term55 _127848 f x).
Proof. exact (@lem6970295 _127848 f x s h1 (@lem6970294)). Qed.
Lemma lem6970298 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6970299 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem6970298 nat t2 t1). Qed.
Lemma lem6970300 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) : (term55 _127848 f x) = (f x).
Proof. exact (@lem6970299 (NUMERAL 0) (f x)). Qed.
Lemma lem6970301 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : (term32 _127848 s f x) = (f x).
Proof. exact (TRANS (@lem6970296 _127848 f x s h1) (@lem6970300 _127848 f x)). Qed.
Lemma lem6970302 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : (term22 _127848 s f x) = (f x).
Proof. exact (TRANS (@lem6970260 _127848 s f x) (@lem6970301 _127848 f x s h1)). Qed.
Lemma lem6970303 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6970304 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : (term35 _127848 s f x) = (term56 _127848 f x).
Proof. exact (MK_COMB (@lem6970303) (@lem6970302 _127848 f x s h1)). Qed.
Lemma lem6970305 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem6970306 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : ((term22 _127848 s f x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem6970304 _127848 f x s h1) (@lem6970305 _127848 f x)). Qed.
Lemma lem6970308 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6970309 (x : nat) : (x = x) = True.
Proof. exact (@lem6970308 nat x). Qed.
Lemma lem6970310 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) : ((f x) = (f x)) = True.
Proof. exact (@lem6970309 (f x)). Qed.
Lemma lem6970311 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) (h1 : @IN _127848 x s) : ((term22 _127848 s f x) = (f x)) = True.
Proof. exact (TRANS (@lem6970306 _127848 f x s h1) (@lem6970310 _127848 f x)). Qed.
Lemma lem6970312 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : term57 _127848 s f x.
Proof. exact (fun h0 : @IN _127848 x s => @lem6970311 _127848 f x s h0). Qed.
Lemma lem6970313 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) : term58 _127848 f x s.
Proof. exact (@lem6970242 _127848 f x s True). Qed.
Lemma lem6970314 {_127848 : Type'} (f : _127848 -> nat) (x : _127848) (s : _127848 -> Prop) : (term59 _127848 s f x) = (term60 _127848 x s).
Proof. exact (@lem6970313 _127848 f x s (@lem6970312 _127848 s f x)). Qed.
Lemma lem6970316 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6970317 {_127848 : Type'} (x : _127848) (s : _127848 -> Prop) : (term60 _127848 x s) = True.
Proof. exact (@lem6970316 (@IN _127848 x s)). Qed.
Lemma lem6970318 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) (x : _127848) : (term59 _127848 s f x) = True.
Proof. exact (TRANS (@lem6970314 _127848 f x s) (@lem6970317 _127848 x s)). Qed.
Lemma lem6970319 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : (term61 _127848 s f) = (term62 _127848).
Proof. exact (fun_ext (fun x : _127848 => @lem6970318 _127848 s f x)). Qed.
Lemma lem6970320 {_127848 : Type'} : (@all _127848) = (@all _127848).
Proof. exact (eq_refl (@all _127848)). Qed.
Lemma lem6970321 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : (term63 _127848 s f) = (term64 _127848).
Proof. exact (MK_COMB (@lem6970320 _127848) (@lem6970319 _127848 s f)). Qed.
Lemma lem6970323 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6970324 {_127848 : Type'} (t : Prop) : (term65 _127848 t) = t.
Proof. exact (@lem6970323 _127848 t). Qed.
Lemma lem6970325 {_127848 : Type'} : (term64 _127848) = True.
Proof. exact (@lem6970324 _127848 True). Qed.
Lemma lem6970326 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : (term63 _127848 s f) = True.
Proof. exact (TRANS (@lem6970321 _127848 s f) (@lem6970325 _127848)). Qed.
Lemma lem6970327 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : True = (term63 _127848 s f).
Proof. exact (SYM (@lem6970326 _127848 s f)). Qed.
Lemma lem6970328 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : term63 _127848 s f.
Proof. exact (EQ_MP (@lem6970327 _127848 s f) (@lem0)). Qed.
Lemma lem6970329 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : (term66 _127848 s f) = (@nsum _127848 s f).
Proof. exact (@lem6970220 _127848 s f (@lem6970328 _127848 s f)). Qed.
Lemma lem6970330 {_127848 : Type'} (s : _127848 -> Prop) (f : _127848 -> nat) : term67 _127848 s f.
Proof. exact (fun h0 : @FINITE _127848 s => @lem6970329 _127848 s f). Qed.
Lemma lem6970335 {_127848 : Type'} (f : _127848 -> nat) : term68 _127848 f.
Proof. exact (fun s : _127848 -> Prop => @lem6970330 _127848 s f). Qed.
Lemma lem6970340 {_127848 : Type'} : term69 _127848.
Proof. exact (fun f : _127848 -> nat => @lem6970335 _127848 f). Qed.
