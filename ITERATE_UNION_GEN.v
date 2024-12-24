Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_UNION_GEN_term_abbrevs.
Require Import ITERATE_SUPPORT_spec.
Require Import ITERATE_UNION_spec.
Require Import SUPPORT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5764204 {_120592 _120607 : Type'} (op : type1400 _120607) : term0 _120592 _120607 op.
Proof. exact (@lem5764203 _120592 _120607 op). Qed.
Lemma lem5764205 {_120592 _120607 : Type'} (op : type1400 _120607) : (term0 _120592 _120607 op) = (term1 _120592 _120607 op).
Proof. exact (eq_refl (term0 _120592 _120607 op)). Qed.
Lemma lem5764206 {_120592 _120607 : Type'} (op : type1400 _120607) : term1 _120592 _120607 op.
Proof. exact (EQ_MP (@lem5764205 _120592 _120607 op) (@lem5764204 _120592 _120607 op)). Qed.
Lemma lem5764207 {_120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : @monoidal _120607 op.
Proof. exact (h1). Qed.
Lemma lem5764208 {_120592 _120607 : Type'} (op : type1400 _120607) (h1 : @monoidal _120607 op) : term2 _120592 _120607 op.
Proof. exact (@lem5764206 _120592 _120607 op (@lem5764207 _120607 op h1)). Qed.
Lemma lem5764209 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term3 _120592 _120607 op f.
Proof. exact (@lem5764208 _120592 _120607 op h1 f). Qed.
Lemma lem5764210 {_120592 _120607 : Type'} (op : type1400 _120607) (f : _120592 -> _120607) : (term3 _120592 _120607 op f) = (term4 _120592 _120607 op f).
Proof. exact (eq_refl (term3 _120592 _120607 op f)). Qed.
Lemma lem5764211 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term4 _120592 _120607 op f.
Proof. exact (EQ_MP (@lem5764210 _120592 _120607 op f) (@lem5764209 _120592 _120607 f op h1)). Qed.
Lemma lem5764212 {_120592 _120607 : Type'} (f : _120592 -> _120607) (s : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term5 _120592 _120607 op f s.
Proof. exact (@lem5764211 _120592 _120607 f op h1 s). Qed.
Lemma lem5764213 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (f : _120592 -> _120607) : (term5 _120592 _120607 op f s) = (term6 _120592 _120607 s op f).
Proof. exact (eq_refl (term5 _120592 _120607 op f s)). Qed.
Lemma lem5764214 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term6 _120592 _120607 s op f.
Proof. exact (EQ_MP (@lem5764213 _120592 _120607 s op f) (@lem5764212 _120592 _120607 f s op h1)). Qed.
Lemma lem5764215 {_120592 _120607 : Type'} (s : _120592 -> Prop) (f : _120592 -> _120607) (t : _120592 -> Prop) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term7 _120592 _120607 s op f t.
Proof. exact (@lem5764214 _120592 _120607 s f op h1 t). Qed.
Lemma lem5764216 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term7 _120592 _120607 s op f t) = (term8 _120592 _120607 s op t f).
Proof. exact (eq_refl (term7 _120592 _120607 s op f t)). Qed.
Lemma lem5764217 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term8 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem5764216 _120592 _120607 s op t f) (@lem5764215 _120592 _120607 s f t op h1)). Qed.
Lemma lem5764218 {_120592 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : term9 _120592 s t) : term9 _120592 s t.
Proof. exact (h1). Qed.
Lemma lem5764219 {_120592 _120607 : Type'} (f : _120592 -> _120607) (op : type1400 _120607) (s : _120592 -> Prop) (t : _120592 -> Prop) (h1 : @monoidal _120607 op) (h2 : term9 _120592 s t) : (term10 _120592 _120607 op s t f) = (term11 _120592 _120607 s op t f).
Proof. exact (@lem5764217 _120592 _120607 s t f op h1 (@lem5764218 _120592 s t h2)). Qed.
Lemma lem5764220 {_120592 _120607 : Type'} (s : _120592 -> Prop) (t : _120592 -> Prop) (f : _120592 -> _120607) (op : type1400 _120607) (h1 : @monoidal _120607 op) : term8 _120592 _120607 s op t f.
Proof. exact (fun h0 : term9 _120592 s t => @lem5764219 _120592 _120607 f op s t h1 h0). Qed.
Lemma lem5764221 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term12 _120592 _120607 s op t f.
Proof. exact (fun h0 : @monoidal _120607 op => @lem5764220 _120592 _120607 s t f op h0). Qed.
Lemma lem5764223 (p : Prop) (q : Prop) (r : Prop) : (term13 p q r) = (term14 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5764228 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : (term12 _120592 _120607 s op t f) = (term15 _120592 _120607 s op t f).
Proof. exact (@lem5764223 (@monoidal _120607 op) (term9 _120592 s t) ((term10 _120592 _120607 op s t f) = (term11 _120592 _120607 s op t f))). Qed.
Lemma lem5764230 {_120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term16 _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5736505 Prop _120011 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5764231 {_120044 _120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term17 _120044 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5764230 Prop _120044 _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5764232 {_120082 _120120 _120158 _120186 _120195 _120196 : Type'} (op : type1400 _120196) : term18 _120082 _120120 _120158 _120186 _120195 _120196 op.
Proof. exact (proj2 (@lem5764231 Prop _120082 _120120 _120158 _120186 _120195 _120196 op)). Qed.
Lemma lem5764265 {_120082 _120196 : Type'} (op : type1400 _120196) : term19 _120082 _120196 op.
Proof. exact (proj1 (@lem5764232 _120082 Prop Prop Prop Prop _120196 op)). Qed.
Lemma lem5764266 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) : term20 _120082 _120196 op f.
Proof. exact (@lem5764265 _120082 _120196 op f). Qed.
Lemma lem5764267 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) : (term20 _120082 _120196 op f) = (term21 _120082 _120196 op f).
Proof. exact (eq_refl (term20 _120082 _120196 op f)). Qed.
Lemma lem5764268 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) : term21 _120082 _120196 op f.
Proof. exact (EQ_MP (@lem5764267 _120082 _120196 op f) (@lem5764266 _120082 _120196 op f)). Qed.
Lemma lem5764269 {_120082 _120196 : Type'} (op : type1400 _120196) (f : _120082 -> _120196) (s : _120082 -> Prop) : term22 _120082 _120196 op f s.
Proof. exact (@lem5764268 _120082 _120196 op f s). Qed.
Lemma lem5764270 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) : (term22 _120082 _120196 op f s) = (term23 _120082 _120196 s op f).
Proof. exact (eq_refl (term22 _120082 _120196 op f s)). Qed.
Lemma lem5764271 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) : term23 _120082 _120196 s op f.
Proof. exact (EQ_MP (@lem5764270 _120082 _120196 s op f) (@lem5764269 _120082 _120196 op f s)). Qed.
Lemma lem5764272 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : term24 _120082 _120196 s op f t.
Proof. exact (@lem5764271 _120082 _120196 s op f t). Qed.
Lemma lem5764273 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : (term24 _120082 _120196 s op f t) = ((term25 _120082 _120196 op f s t) = (term26 _120082 _120196 s op f t)).
Proof. exact (eq_refl (term24 _120082 _120196 s op f t)). Qed.
Lemma lem5764302 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term27 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term27 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5764303 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term27 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f).
Proof. exact (SYM (@lem5764302 _120296 _120308 op s f h1)). Qed.
Lemma lem5764304 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem5764305 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f)) : (term27 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem5764304 _120296 _120308 op s f h1)). Qed.
Lemma lem5764306 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term27 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term27 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem5764303 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f) => @lem5764305 _120296 _120308 op s f h1)). Qed.
Lemma lem5764307 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term28 _120296 _120308 op f) = (term29 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem5764306 _120296 _120308 op s f)). Qed.
Lemma lem5764308 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem5764309 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term30 _120296 _120308 op f) = (term31 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem5764308 _120308) (@lem5764307 _120296 _120308 op f)). Qed.
Lemma lem5764310 {_120296 _120308 : Type'} (op : type1400 _120296) : (term32 _120296 _120308 op) = (term33 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem5764309 _120296 _120308 op f)). Qed.
Lemma lem5764311 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem5764312 {_120296 _120308 : Type'} (op : type1400 _120296) : (term34 _120296 _120308 op) = (term35 _120296 _120308 op).
Proof. exact (MK_COMB (@lem5764311 _120296 _120308) (@lem5764310 _120296 _120308 op)). Qed.
Lemma lem5764313 {_120296 _120308 : Type'} : (term36 _120296 _120308) = (term37 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem5764312 _120296 _120308 op)). Qed.
Lemma lem5764314 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem5764315 {_120296 _120308 : Type'} : (term38 _120296 _120308) = (term39 _120296 _120308).
Proof. exact (MK_COMB (@lem5764314 _120296) (@lem5764313 _120296 _120308)). Qed.
Lemma lem5764316 {_120296 _120308 : Type'} : term39 _120296 _120308.
Proof. exact (EQ_MP (@lem5764315 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem5764317 {_120296 _120308 : Type'} (op : type1400 _120296) : term40 _120296 _120308 op.
Proof. exact (@lem5764316 _120296 _120308 op). Qed.
Lemma lem5764318 {_120296 _120308 : Type'} (op : type1400 _120296) : (term40 _120296 _120308 op) = (term35 _120296 _120308 op).
Proof. exact (eq_refl (term40 _120296 _120308 op)). Qed.
Lemma lem5764319 {_120296 _120308 : Type'} (op : type1400 _120296) : term35 _120296 _120308 op.
Proof. exact (EQ_MP (@lem5764318 _120296 _120308 op) (@lem5764317 _120296 _120308 op)). Qed.
Lemma lem5764320 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term41 _120296 _120308 op f.
Proof. exact (@lem5764319 _120296 _120308 op f). Qed.
Lemma lem5764321 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term41 _120296 _120308 op f) = (term31 _120296 _120308 op f).
Proof. exact (eq_refl (term41 _120296 _120308 op f)). Qed.
Lemma lem5764322 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term31 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem5764321 _120296 _120308 op f) (@lem5764320 _120296 _120308 op f)). Qed.
Lemma lem5764323 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term42 _120296 _120308 op f s.
Proof. exact (@lem5764322 _120296 _120308 op f s). Qed.
Lemma lem5764324 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term42 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f)).
Proof. exact (eq_refl (term42 _120296 _120308 op f s)). Qed.
Lemma lem5764353 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5764324 _120296 _120308 op s f) (@lem5764323 _120296 _120308 op f s)). Qed.
Lemma lem5764354 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term43 A B op s f).
Proof. exact (@lem5764353 B A op s f). Qed.
Lemma lem5764355 {A B : Type'} (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term10 A B op s t f) = (term44 A B op s t f).
Proof. exact (@lem5764354 A B op (@UNION A s t) f). Qed.
Lemma lem5764356 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5764357 {A B : Type'} (op : type1400 B) (s : A -> Prop) (t : A -> Prop) (f : A -> B) : (term45 A B op s t f) = (term46 A B op s t f).
Proof. exact (MK_COMB (@lem5764356 B) (@lem5764355 A B op s t f)). Qed.
Lemma lem5764359 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5764324 _120296 _120308 op s f) (@lem5764323 _120296 _120308 op f s)). Qed.
Lemma lem5764360 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term43 A B op s f).
Proof. exact (@lem5764359 B A op s f). Qed.
Lemma lem5764361 {B : Type'} (op : type1400 B) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5764362 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term47 A B op s f) = (term48 A B op s f).
Proof. exact (MK_COMB (@lem5764361 B op) (@lem5764360 A B op s f)). Qed.
Lemma lem5764364 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term27 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem5764324 _120296 _120308 op s f) (@lem5764323 _120296 _120308 op f s)). Qed.
Lemma lem5764365 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (term43 A B op s f).
Proof. exact (@lem5764364 B A op s f). Qed.
Lemma lem5764366 {A B : Type'} (op : type1400 B) (t : A -> Prop) (f : A -> B) : (@iterate B A op t f) = (term43 A B op t f).
Proof. exact (@lem5764365 A B op t f). Qed.
Lemma lem5764367 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term11 A B s op t f) = (term49 A B s op t f).
Proof. exact (MK_COMB (@lem5764362 A B op s f) (@lem5764366 A B op t f)). Qed.
Lemma lem5764368 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : ((term10 A B op s t f) = (term11 A B s op t f)) = ((term44 A B op s t f) = (term49 A B s op t f)).
Proof. exact (MK_COMB (@lem5764357 A B op s t f) (@lem5764367 A B s op t f)). Qed.
Lemma lem5764369 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term50 A B s op f t) = (term50 A B s op f t).
Proof. exact (eq_refl (term50 A B s op f t)). Qed.
Lemma lem5764370 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term51 A B s op t f) = (term52 A B s op t f).
Proof. exact (MK_COMB (@lem5764369 A B s op f t) (@lem5764368 A B s op t f)). Qed.
Lemma lem5764371 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) : (term53 A B s op f) = (term54 A B s op f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5764370 A B s op t f)). Qed.
Lemma lem5764372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5764373 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) : (term55 A B s op f) = (term56 A B s op f).
Proof. exact (MK_COMB (@lem5764372 A) (@lem5764371 A B s op f)). Qed.
Lemma lem5764374 {A B : Type'} (op : type1400 B) (f : A -> B) : (term57 A B op f) = (term58 A B op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5764373 A B s op f)). Qed.
Lemma lem5764375 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5764376 {A B : Type'} (op : type1400 B) (f : A -> B) : (term59 A B op f) = (term60 A B op f).
Proof. exact (MK_COMB (@lem5764375 A) (@lem5764374 A B op f)). Qed.
Lemma lem5764377 {A B : Type'} (op : type1400 B) : (term61 A B op) = (term62 A B op).
Proof. exact (fun_ext (fun f : A -> B => @lem5764376 A B op f)). Qed.
Lemma lem5764378 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5764379 {A B : Type'} (op : type1400 B) : (term63 A B op) = (term64 A B op).
Proof. exact (MK_COMB (@lem5764378 A B) (@lem5764377 A B op)). Qed.
Lemma lem5764380 {B : Type'} (op : type1400 B) : (term65 B op) = (term65 B op).
Proof. exact (eq_refl (term65 B op)). Qed.
Lemma lem5764381 {A B : Type'} (op : type1400 B) : (term66 A B op) = (term67 A B op).
Proof. exact (MK_COMB (@lem5764380 B op) (@lem5764379 A B op)). Qed.
Lemma lem5764382 {A B : Type'} : (term68 A B) = (term69 A B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5764381 A B op)). Qed.
Lemma lem5764383 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5764384 {A B : Type'} : (term70 A B) = (term71 A B).
Proof. exact (MK_COMB (@lem5764383 B) (@lem5764382 A B)). Qed.
Lemma lem5764385 {A B : Type'} : (term71 A B) = (term70 A B).
Proof. exact (SYM (@lem5764384 A B)). Qed.
Lemma lem5764393 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term72 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5764394 (p : Prop) (q : Prop) (p' : Prop) : term73 p q p'.
Proof. exact (fun q' : Prop => @lem5764393 p q p' q'). Qed.
Lemma lem5764395 (p : Prop) (q : Prop) : term74 p q.
Proof. exact (fun p' : Prop => @lem5764394 p q p'). Qed.
Lemma lem5764396 {A B : Type'} (op : type1400 B) : term75 A B op.
Proof. exact (@lem5764395 (@monoidal B op) (term64 A B op)). Qed.
Lemma lem5764397 {A B : Type'} (op : type1400 B) (p' : Prop) : term76 A B op p'.
Proof. exact (@lem5764396 A B op p'). Qed.
Lemma lem5764398 {A B : Type'} (op : type1400 B) (p' : Prop) : (term76 A B op p') = (term77 A B op p').
Proof. exact (eq_refl (term76 A B op p')). Qed.
Lemma lem5764399 {A B : Type'} (op : type1400 B) (p' : Prop) : term77 A B op p'.
Proof. exact (EQ_MP (@lem5764398 A B op p') (@lem5764397 A B op p')). Qed.
Lemma lem5764400 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : term78 A B op p' q'.
Proof. exact (@lem5764399 A B op p' q'). Qed.
Lemma lem5764401 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : (term78 A B op p' q') = (term79 A B op p' q').
Proof. exact (eq_refl (term78 A B op p' q')). Qed.
Lemma lem5764402 {A B : Type'} (op : type1400 B) (p' : Prop) (q' : Prop) : term79 A B op p' q'.
Proof. exact (EQ_MP (@lem5764401 A B op p' q') (@lem5764400 A B op p' q')). Qed.
Lemma lem5764403 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@monoidal B op).
Proof. exact (eq_refl (@monoidal B op)). Qed.
Lemma lem5764404 {A B : Type'} (op : type1400 B) (q' : Prop) : term80 A B op q'.
Proof. exact (@lem5764402 A B op (@monoidal B op) q'). Qed.
Lemma lem5764405 {A B : Type'} (op : type1400 B) (q' : Prop) : term81 A B op q'.
Proof. exact (@lem5764404 A B op q' (@lem5764403 B op)). Qed.
Lemma lem5764406 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5764407 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5764424 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term72 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5764425 (p : Prop) (q : Prop) (p' : Prop) : term73 p q p'.
Proof. exact (fun q' : Prop => @lem5764424 p q p' q'). Qed.
Lemma lem5764426 (p : Prop) (q : Prop) : term74 p q.
Proof. exact (fun p' : Prop => @lem5764425 p q p'). Qed.
Lemma lem5764427 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term82 A B s op t f.
Proof. exact (@lem5764426 (term83 A B s op f t) ((term44 A B op s t f) = (term49 A B s op t f))). Qed.
Lemma lem5764428 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term84 A B s op t f p'.
Proof. exact (@lem5764427 A B s op t f p'). Qed.
Lemma lem5764429 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : (term84 A B s op t f p') = (term85 A B s op t f p').
Proof. exact (eq_refl (term84 A B s op t f p')). Qed.
Lemma lem5764430 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) : term85 A B s op t f p'.
Proof. exact (EQ_MP (@lem5764429 A B s op t f p') (@lem5764428 A B s op t f p')). Qed.
Lemma lem5764431 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term86 A B s op t f p' q'.
Proof. exact (@lem5764430 A B s op t f p' q'). Qed.
Lemma lem5764432 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term86 A B s op t f p' q') = (term87 A B s op t f p' q').
Proof. exact (eq_refl (term86 A B s op t f p' q')). Qed.
Lemma lem5764433 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term87 A B s op t f p' q'.
Proof. exact (EQ_MP (@lem5764432 A B s op t f p' q') (@lem5764431 A B s op t f p' q')). Qed.
Lemma lem5764438 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term83 A B s op f t) = (term83 A B s op f t).
Proof. exact (eq_refl (term83 A B s op f t)). Qed.
Lemma lem5764439 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (q' : Prop) : term88 A B s op f t q'.
Proof. exact (@lem5764433 A B s op t f (term83 A B s op f t) q'). Qed.
Lemma lem5764440 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (q' : Prop) : term89 A B s op f t q'.
Proof. exact (@lem5764439 A B s op f t q' (@lem5764438 A B s op f t)). Qed.
Lemma lem5764441 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : term83 A B s op f t.
Proof. exact (h1). Qed.
Lemma lem5764442 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : term90 A B s op f t.
Proof. exact (proj2 (@lem5764441 A B s op f t h1)). Qed.
Lemma lem5764443 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : term91 A B s op f t.
Proof. exact (proj2 (@lem5764442 A B s op f t h1)). Qed.
Lemma lem5764444 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term91 A B s op f t) = ((term91 A B s op f t) = True).
Proof. exact (@lem7 (term91 A B s op f t)). Qed.
Lemma lem5764446 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : term92 A B op f t.
Proof. exact (proj1 (@lem5764442 A B s op f t h1)). Qed.
Lemma lem5764447 {A B : Type'} (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term92 A B op f t) = ((term92 A B op f t) = True).
Proof. exact (@lem7 (term92 A B op f t)). Qed.
Lemma lem5764449 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : term92 A B op f s.
Proof. exact (proj1 (@lem5764441 A B s op f t h1)). Qed.
Lemma lem5764450 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term92 A B op f s) = ((term92 A B op f s) = True).
Proof. exact (@lem7 (term92 A B op f s)). Qed.
Lemma lem5764455 {_120082 _120196 : Type'} (s : _120082 -> Prop) (op : type1400 _120196) (f : _120082 -> _120196) (t : _120082 -> Prop) : (term25 _120082 _120196 op f s t) = (term26 _120082 _120196 s op f t).
Proof. exact (EQ_MP (@lem5764273 _120082 _120196 s op f t) (@lem5764272 _120082 _120196 s op f t)). Qed.
Lemma lem5764456 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term25 A B op f s t) = (term26 A B s op f t).
Proof. exact (@lem5764455 A B s op f t). Qed.
Lemma lem5764457 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5764458 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term93 A B op f s t) = (term94 A B s op f t).
Proof. exact (MK_COMB (@lem5764457 A B op) (@lem5764456 A B s op f t)). Qed.
Lemma lem5764459 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5764460 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term44 A B op s t f) = (term95 A B s op t f).
Proof. exact (MK_COMB (@lem5764458 A B s op f t) (@lem5764459 A B f)). Qed.
Lemma lem5764462 {_120592 _120607 : Type'} (s : _120592 -> Prop) (op : type1400 _120607) (t : _120592 -> Prop) (f : _120592 -> _120607) : term15 _120592 _120607 s op t f.
Proof. exact (EQ_MP (@lem5764228 _120592 _120607 s op t f) (@lem5764221 _120592 _120607 s op t f)). Qed.
Lemma lem5764463 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term15 A B s op t f.
Proof. exact (@lem5764462 A B s op t f). Qed.
Lemma lem5764464 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : term96 A B s op t f.
Proof. exact (@lem5764463 A B (@support A B op f s) op (@support A B op f t) f). Qed.
Lemma lem5764468 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5764407 B op) (@lem5764406 B op h1)). Qed.
Lemma lem5764469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764470 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term97 B op) = (and True).
Proof. exact (MK_COMB (@lem5764469) (@lem5764468 B op h1)). Qed.
Lemma lem5764474 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term92 A B op f s) = True.
Proof. exact (EQ_MP (@lem5764450 A B op f s) (@lem5764449 A B s op f t h1)). Qed.
Lemma lem5764475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764476 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term98 A B op f s) = (and True).
Proof. exact (MK_COMB (@lem5764475) (@lem5764474 A B s op f t h1)). Qed.
Lemma lem5764480 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term92 A B op f t) = True.
Proof. exact (EQ_MP (@lem5764447 A B op f t) (@lem5764446 A B s op f t h1)). Qed.
Lemma lem5764481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5764482 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term98 A B op f t) = (and True).
Proof. exact (MK_COMB (@lem5764481) (@lem5764480 A B s op f t h1)). Qed.
Lemma lem5764484 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term91 A B s op f t) = True.
Proof. exact (EQ_MP (@lem5764444 A B s op f t) (@lem5764443 A B s op f t h1)). Qed.
Lemma lem5764485 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term90 A B s op f t) = (True /\ True).
Proof. exact (MK_COMB (@lem5764482 A B s op f t h1) (@lem5764484 A B s op f t h1)). Qed.
Lemma lem5764487 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5764488 : (True /\ True) = True.
Proof. exact (@lem5764487 True). Qed.
Lemma lem5764489 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term90 A B s op f t) = True.
Proof. exact (TRANS (@lem5764485 A B s op f t h1) (@lem5764488)). Qed.
Lemma lem5764490 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term83 A B s op f t) = (True /\ True).
Proof. exact (MK_COMB (@lem5764476 A B s op f t h1) (@lem5764489 A B s op f t h1)). Qed.
Lemma lem5764492 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5764493 : (True /\ True) = True.
Proof. exact (@lem5764492 True). Qed.
Lemma lem5764494 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : term83 A B s op f t) : (term83 A B s op f t) = True.
Proof. exact (TRANS (@lem5764490 A B s op f t h1) (@lem5764493)). Qed.
Lemma lem5764495 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : (term99 A B s op f t) = (True /\ True).
Proof. exact (MK_COMB (@lem5764470 B op h1) (@lem5764494 A B s op f t h2)). Qed.
Lemma lem5764497 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5764498 : (True /\ True) = True.
Proof. exact (@lem5764497 True). Qed.
Lemma lem5764499 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : (term99 A B s op f t) = True.
Proof. exact (TRANS (@lem5764495 A B s op f t h1 h2) (@lem5764498)). Qed.
Lemma lem5764500 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : True = (term99 A B s op f t).
Proof. exact (SYM (@lem5764499 A B s op f t h1 h2)). Qed.
Lemma lem5764501 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : term99 A B s op f t.
Proof. exact (EQ_MP (@lem5764500 A B s op f t h1 h2) (@lem0)). Qed.
Lemma lem5764502 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : (term95 A B s op t f) = (term49 A B s op t f).
Proof. exact (@lem5764464 A B s op t f (@lem5764501 A B s op f t h1 h2)). Qed.
Lemma lem5764503 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : (term44 A B op s t f) = (term49 A B s op t f).
Proof. exact (TRANS (@lem5764460 A B s op t f) (@lem5764502 A B s op f t h1 h2)). Qed.
Lemma lem5764504 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem5764505 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : (term46 A B op s t f) = (term100 A B s op t f).
Proof. exact (MK_COMB (@lem5764504 B) (@lem5764503 A B s op f t h1 h2)). Qed.
Lemma lem5764506 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : (term49 A B s op t f) = (term49 A B s op t f).
Proof. exact (eq_refl (term49 A B s op t f)). Qed.
Lemma lem5764507 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : ((term44 A B op s t f) = (term49 A B s op t f)) = ((term49 A B s op t f) = (term49 A B s op t f)).
Proof. exact (MK_COMB (@lem5764505 A B s op f t h1 h2) (@lem5764506 A B s op t f)). Qed.
Lemma lem5764509 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5764510 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem5764509 B x). Qed.
Lemma lem5764511 {A B : Type'} (s : A -> Prop) (op : type1400 B) (t : A -> Prop) (f : A -> B) : ((term49 A B s op t f) = (term49 A B s op t f)) = True.
Proof. exact (@lem5764510 B (term49 A B s op t f)). Qed.
Lemma lem5764512 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) (h1 : @monoidal B op) (h2 : term83 A B s op f t) : ((term44 A B op s t f) = (term49 A B s op t f)) = True.
Proof. exact (TRANS (@lem5764507 A B s op f t h1 h2) (@lem5764511 A B s op t f)). Qed.
Lemma lem5764513 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term101 A B s op t f.
Proof. exact (fun h0 : term83 A B s op f t => @lem5764512 A B s op f t h1 h0). Qed.
Lemma lem5764514 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : term102 A B s op f t.
Proof. exact (@lem5764440 A B s op f t True). Qed.
Lemma lem5764515 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : (term52 A B s op t f) = (term103 A B s op f t).
Proof. exact (@lem5764514 A B s op f t (@lem5764513 A B s t f op h1)). Qed.
Lemma lem5764517 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5764518 {A B : Type'} (s : A -> Prop) (op : type1400 B) (f : A -> B) (t : A -> Prop) : (term103 A B s op f t) = True.
Proof. exact (@lem5764517 (term83 A B s op f t)). Qed.
Lemma lem5764519 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term52 A B s op t f) = True.
Proof. exact (TRANS (@lem5764515 A B s f t op h1) (@lem5764518 A B s op f t)). Qed.
Lemma lem5764520 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term54 A B s op f) = (term104 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5764519 A B s t f op h1)). Qed.
Lemma lem5764521 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5764522 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term56 A B s op f) = (term105 A).
Proof. exact (MK_COMB (@lem5764521 A) (@lem5764520 A B s f op h1)). Qed.
Lemma lem5764524 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5764525 {A : Type'} (t : Prop) : (term107 A t) = t.
Proof. exact (@lem5764524 (A -> Prop) t). Qed.
Lemma lem5764526 {A : Type'} : (term105 A) = True.
Proof. exact (@lem5764525 A True). Qed.
Lemma lem5764527 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term56 A B s op f) = True.
Proof. exact (TRANS (@lem5764522 A B s f op h1) (@lem5764526 A)). Qed.
Lemma lem5764528 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term58 A B op f) = (term104 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5764527 A B s f op h1)). Qed.
Lemma lem5764529 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5764530 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term60 A B op f) = (term105 A).
Proof. exact (MK_COMB (@lem5764529 A) (@lem5764528 A B f op h1)). Qed.
Lemma lem5764532 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5764533 {A : Type'} (t : Prop) : (term107 A t) = t.
Proof. exact (@lem5764532 (A -> Prop) t). Qed.
Lemma lem5764534 {A : Type'} : (term105 A) = True.
Proof. exact (@lem5764533 A True). Qed.
Lemma lem5764535 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term60 A B op f) = True.
Proof. exact (TRANS (@lem5764530 A B f op h1) (@lem5764534 A)). Qed.
Lemma lem5764536 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term62 A B op) = (term108 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5764535 A B f op h1)). Qed.
Lemma lem5764537 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5764538 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term64 A B op) = (term109 A B).
Proof. exact (MK_COMB (@lem5764537 A B) (@lem5764536 A B op h1)). Qed.
Lemma lem5764540 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5764541 {A B : Type'} (t : Prop) : (term110 A B t) = t.
Proof. exact (@lem5764540 (A -> B) t). Qed.
Lemma lem5764542 {A B : Type'} : (term109 A B) = True.
Proof. exact (@lem5764541 A B True). Qed.
Lemma lem5764543 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (term64 A B op) = True.
Proof. exact (TRANS (@lem5764538 A B op h1) (@lem5764542 A B)). Qed.
Lemma lem5764544 {A B : Type'} (op : type1400 B) : term111 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5764543 A B op h0). Qed.
Lemma lem5764545 {A B : Type'} (op : type1400 B) : term112 A B op.
Proof. exact (@lem5764405 A B op True). Qed.
Lemma lem5764546 {A B : Type'} (op : type1400 B) : (term67 A B op) = (term113 B op).
Proof. exact (@lem5764545 A B op (@lem5764544 A B op)). Qed.
Lemma lem5764548 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5764549 {B : Type'} (op : type1400 B) : (term113 B op) = True.
Proof. exact (@lem5764548 (@monoidal B op)). Qed.
Lemma lem5764550 {A B : Type'} (op : type1400 B) : (term67 A B op) = True.
Proof. exact (TRANS (@lem5764546 A B op) (@lem5764549 B op)). Qed.
Lemma lem5764551 {A B : Type'} : (term69 A B) = (term114 B).
Proof. exact (fun_ext (fun op : type1400 B => @lem5764550 A B op)). Qed.
Lemma lem5764552 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5764553 {A B : Type'} : (term71 A B) = (term115 B).
Proof. exact (MK_COMB (@lem5764552 B) (@lem5764551 A B)). Qed.
Lemma lem5764555 {A : Type'} (t : Prop) : (term106 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5764556 {B : Type'} (t : Prop) : (term116 B t) = t.
Proof. exact (@lem5764555 (type1400 B) t). Qed.
Lemma lem5764557 {B : Type'} : (term115 B) = True.
Proof. exact (@lem5764556 B True). Qed.
Lemma lem5764558 {A B : Type'} : (term71 A B) = True.
Proof. exact (TRANS (@lem5764553 A B) (@lem5764557 B)). Qed.
Lemma lem5764559 {A B : Type'} : True = (term71 A B).
Proof. exact (SYM (@lem5764558 A B)). Qed.
Lemma lem5764560 {A B : Type'} : term71 A B.
Proof. exact (EQ_MP (@lem5764559 A B) (@lem0)). Qed.
Lemma lem5764561 {A B : Type'} : term70 A B.
Proof. exact (EQ_MP (@lem5764385 A B) (@lem5764560 A B)). Qed.
