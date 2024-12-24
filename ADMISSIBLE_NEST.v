Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_NEST_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import admissible_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Lemma lem8131068 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8131069 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8131070 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8131069 t1) (@lem8131068 t1)). Qed.
Lemma lem8131071 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8131070 t1 t2). Qed.
Lemma lem8131072 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8131073 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8131072 t1 t2) (@lem8131071 t1 t2)). Qed.
Lemma lem8131074 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8131073 t1 t2 t3). Qed.
Lemma lem8131075 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8131076 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8131075 t1 t2 t3) (@lem8131074 t1 t2 t3)). Qed.
Lemma lem8131077 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8131076 t1 t2 t3)). Qed.
Lemma lem8131078 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term7 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8131079 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term7 _143449 _143452 _143456 _143457 _143462 p) = (term8 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term7 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8131080 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term8 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8131079 _143449 _143452 _143456 _143457 _143462 p) (@lem8131078 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8131081 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term9 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8131080 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8131082 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term9 _143449 _143452 _143456 _143457 _143462 p lt2) = (term10 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term9 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8131083 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term10 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8131082 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8131081 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8131084 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term11 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8131083 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8131085 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term11 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term12 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term11 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8131086 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term12 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8131085 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8131084 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8131087 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8131086 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8131088 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term13 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8131111 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8131088 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8131087 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8131112 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (@admissible A B A A P lt2 p s t) = (term15 A B P p lt2 s t).
Proof. exact (@lem8131111 A B A A P p lt2 s t). Qed.
Lemma lem8131141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8131142 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term16 A B P lt2 p s t) = (term17 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131141) (@lem8131112 A B P p lt2 s t)). Qed.
Lemma lem8131153 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term18 A B P p lt2 t s) = (term18 A B P p lt2 t s).
Proof. exact (eq_refl (term18 A B P p lt2 t s)). Qed.
Lemma lem8131154 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term19 A B P p lt2 t s) = (term20 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8131142 A B P p lt2 s t) (@lem8131153 A B P p lt2 t s)). Qed.
Lemma lem8131157 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8131158 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term21 A B P p lt2 t s) = (term22 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8131157) (@lem8131154 A B P p lt2 t s)). Qed.
Lemma lem8131160 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term14 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8131088 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8131087 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8131161 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (@admissible A B A B P lt2 p s t) = (term23 A B P p lt2 s t).
Proof. exact (@lem8131160 A B A B P p lt2 s t). Qed.
Lemma lem8131162 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term24 A B P lt2 p s t) = (term25 A B P p lt2 s t).
Proof. exact (@lem8131161 A B P p lt2 s (term26 A B P t)). Qed.
Lemma lem8131192 {A B : Type'} (f : A -> B) (y : A) : (term27 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8131193 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term28 A B P f y) = (f y).
Proof. exact (@lem8131192 (A -> B) (P -> B) f y). Qed.
Lemma lem8131194 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term29 A B P t f) = (term30 A B P t f).
Proof. exact (@lem8131193 A B P (term26 A B P t) f). Qed.
Lemma lem8131195 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term30 A B P t f) = (term31 A B P t f).
Proof. exact (eq_refl (term30 A B P t f)). Qed.
Lemma lem8131196 {A B P : Type'} (t : type557 A B P) : (term32 A B P t) = (term26 A B P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131195 A B P t f)). Qed.
Lemma lem8131197 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8131198 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term29 A B P t f) = (term30 A B P t f).
Proof. exact (MK_COMB (@lem8131196 A B P t) (@lem8131197 A B f)). Qed.
Lemma lem8131199 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8131200 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term33 A B P t f) = (term34 A B P t f).
Proof. exact (MK_COMB (@lem8131199 B P) (@lem8131198 A B P t f)). Qed.
Lemma lem8131201 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term30 A B P t f) = (term31 A B P t f).
Proof. exact (eq_refl (term30 A B P t f)). Qed.
Lemma lem8131202 {A B P : Type'} (t : type557 A B P) (f : A -> B) : ((term29 A B P t f) = (term30 A B P t f)) = ((term30 A B P t f) = (term31 A B P t f)).
Proof. exact (MK_COMB (@lem8131200 A B P t f) (@lem8131201 A B P t f)). Qed.
Lemma lem8131203 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term30 A B P t f) = (term31 A B P t f).
Proof. exact (EQ_MP (@lem8131202 A B P t f) (@lem8131194 A B P t f)). Qed.
Lemma lem8131204 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8131205 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term35 A B P t f a) = (term36 A B P t f a).
Proof. exact (MK_COMB (@lem8131203 A B P t f) (@lem8131204 P a)). Qed.
Lemma lem8131207 {A B : Type'} (f : A -> B) (y : A) : (term27 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8131208 {B P : Type'} (f : P -> B) (y : P) : (term37 B P f y) = (f y).
Proof. exact (@lem8131207 P B f y). Qed.
Lemma lem8131209 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term38 A B P t f a) = (term36 A B P t f a).
Proof. exact (@lem8131208 B P (term31 A B P t f) a). Qed.
Lemma lem8131210 {A B P : Type'} (t : type557 A B P) (f : A -> B) (x : P) : (term36 A B P t f x) = (term39 A B P t f x).
Proof. exact (eq_refl (term36 A B P t f x)). Qed.
Lemma lem8131211 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term40 A B P t f) = (term31 A B P t f).
Proof. exact (fun_ext (fun x : P => @lem8131210 A B P t f x)). Qed.
Lemma lem8131212 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8131213 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term38 A B P t f a) = (term36 A B P t f a).
Proof. exact (MK_COMB (@lem8131211 A B P t f) (@lem8131212 P a)). Qed.
Lemma lem8131214 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8131215 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term41 A B P t f a) = (term42 A B P t f a).
Proof. exact (MK_COMB (@lem8131214 B) (@lem8131213 A B P t f a)). Qed.
Lemma lem8131216 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term36 A B P t f a) = (term39 A B P t f a).
Proof. exact (eq_refl (term36 A B P t f a)). Qed.
Lemma lem8131217 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : ((term38 A B P t f a) = (term36 A B P t f a)) = ((term36 A B P t f a) = (term39 A B P t f a)).
Proof. exact (MK_COMB (@lem8131215 A B P t f a) (@lem8131216 A B P t f a)). Qed.
Lemma lem8131218 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term36 A B P t f a) = (term39 A B P t f a).
Proof. exact (EQ_MP (@lem8131217 A B P t f a) (@lem8131209 A B P t f a)). Qed.
Lemma lem8131219 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term35 A B P t f a) = (term39 A B P t f a).
Proof. exact (TRANS (@lem8131205 A B P t f a) (@lem8131218 A B P t f a)). Qed.
Lemma lem8131220 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8131221 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term43 A B P t f a) = (term44 A B P t f a).
Proof. exact (MK_COMB (@lem8131220 B) (@lem8131219 A B P t f a)). Qed.
Lemma lem8131223 {A B : Type'} (f : A -> B) (y : A) : (term27 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8131224 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term28 A B P f y) = (f y).
Proof. exact (@lem8131223 (A -> B) (P -> B) f y). Qed.
Lemma lem8131225 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (term29 A B P t g) = (term30 A B P t g).
Proof. exact (@lem8131224 A B P (term26 A B P t) g). Qed.
Lemma lem8131226 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (term30 A B P t f) = (term31 A B P t f).
Proof. exact (eq_refl (term30 A B P t f)). Qed.
Lemma lem8131227 {A B P : Type'} (t : type557 A B P) : (term32 A B P t) = (term26 A B P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131226 A B P t f)). Qed.
Lemma lem8131228 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8131229 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (term29 A B P t g) = (term30 A B P t g).
Proof. exact (MK_COMB (@lem8131227 A B P t) (@lem8131228 A B g)). Qed.
Lemma lem8131230 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8131231 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (term33 A B P t g) = (term34 A B P t g).
Proof. exact (MK_COMB (@lem8131230 B P) (@lem8131229 A B P t g)). Qed.
Lemma lem8131232 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (term30 A B P t g) = (term31 A B P t g).
Proof. exact (eq_refl (term30 A B P t g)). Qed.
Lemma lem8131233 {A B P : Type'} (t : type557 A B P) (g : A -> B) : ((term29 A B P t g) = (term30 A B P t g)) = ((term30 A B P t g) = (term31 A B P t g)).
Proof. exact (MK_COMB (@lem8131231 A B P t g) (@lem8131232 A B P t g)). Qed.
Lemma lem8131234 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (term30 A B P t g) = (term31 A B P t g).
Proof. exact (EQ_MP (@lem8131233 A B P t g) (@lem8131225 A B P t g)). Qed.
Lemma lem8131235 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8131236 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term35 A B P t g a) = (term36 A B P t g a).
Proof. exact (MK_COMB (@lem8131234 A B P t g) (@lem8131235 P a)). Qed.
Lemma lem8131238 {A B : Type'} (f : A -> B) (y : A) : (term27 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8131239 {B P : Type'} (f : P -> B) (y : P) : (term37 B P f y) = (f y).
Proof. exact (@lem8131238 P B f y). Qed.
Lemma lem8131240 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term38 A B P t g a) = (term36 A B P t g a).
Proof. exact (@lem8131239 B P (term31 A B P t g) a). Qed.
Lemma lem8131241 {A B P : Type'} (t : type557 A B P) (g : A -> B) (x : P) : (term36 A B P t g x) = (term39 A B P t g x).
Proof. exact (eq_refl (term36 A B P t g x)). Qed.
Lemma lem8131242 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (term40 A B P t g) = (term31 A B P t g).
Proof. exact (fun_ext (fun x : P => @lem8131241 A B P t g x)). Qed.
Lemma lem8131243 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8131244 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term38 A B P t g a) = (term36 A B P t g a).
Proof. exact (MK_COMB (@lem8131242 A B P t g) (@lem8131243 P a)). Qed.
Lemma lem8131245 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8131246 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term41 A B P t g a) = (term42 A B P t g a).
Proof. exact (MK_COMB (@lem8131245 B) (@lem8131244 A B P t g a)). Qed.
Lemma lem8131247 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term36 A B P t g a) = (term39 A B P t g a).
Proof. exact (eq_refl (term36 A B P t g a)). Qed.
Lemma lem8131248 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : ((term38 A B P t g a) = (term36 A B P t g a)) = ((term36 A B P t g a) = (term39 A B P t g a)).
Proof. exact (MK_COMB (@lem8131246 A B P t g a) (@lem8131247 A B P t g a)). Qed.
Lemma lem8131249 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term36 A B P t g a) = (term39 A B P t g a).
Proof. exact (EQ_MP (@lem8131248 A B P t g a) (@lem8131240 A B P t g a)). Qed.
Lemma lem8131250 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term35 A B P t g a) = (term39 A B P t g a).
Proof. exact (TRANS (@lem8131236 A B P t g a) (@lem8131249 A B P t g a)). Qed.
Lemma lem8131251 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term35 A B P t f a) = (term35 A B P t g a)) = ((term39 A B P t f a) = (term39 A B P t g a)).
Proof. exact (MK_COMB (@lem8131221 A B P t f a) (@lem8131250 A B P t g a)). Qed.
Lemma lem8131254 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term45 A B P p lt2 s a f g) = (term45 A B P p lt2 s a f g).
Proof. exact (eq_refl (term45 A B P p lt2 s a f g)). Qed.
Lemma lem8131255 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term46 A B P p lt2 s f t g a) = (term47 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131254 A B P p lt2 s a f g) (@lem8131251 A B P f t g a)). Qed.
Lemma lem8131258 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term48 A B P p lt2 s f t g) = (term49 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8131255 A B P p lt2 s f t g a)). Qed.
Lemma lem8131259 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131260 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term50 A B P p lt2 s f t g) = (term51 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131259 P) (@lem8131258 A B P p lt2 s f t g)). Qed.
Lemma lem8131265 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term52 A B P p lt2 s f t) = (term53 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8131260 A B P p lt2 s f t g)). Qed.
Lemma lem8131266 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131267 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term54 A B P p lt2 s f t) = (term55 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131266 A B) (@lem8131265 A B P p lt2 s f t)). Qed.
Lemma lem8131272 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term56 A B P p lt2 s t) = (term57 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131267 A B P p lt2 s f t)). Qed.
Lemma lem8131273 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131274 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term25 A B P p lt2 s t) = (term58 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131273 A B) (@lem8131272 A B P p lt2 s t)). Qed.
Lemma lem8131279 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term24 A B P lt2 p s t) = (term58 A B P p lt2 s t).
Proof. exact (TRANS (@lem8131162 A B P p lt2 s t) (@lem8131274 A B P p lt2 s t)). Qed.
Lemma lem8131280 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term59 A B P lt2 p s t) = (term60 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131158 A B P p lt2 t s) (@lem8131279 A B P p lt2 s t)). Qed.
Lemma lem8131283 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term61 A B P lt2 p s) = (term62 A B P p lt2 s).
Proof. exact (fun_ext (fun t : type557 A B P => @lem8131280 A B P p lt2 s t)). Qed.
Lemma lem8131284 {A B P : Type'} : (@all ((A -> B) -> P -> A)) = (@all ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> A))). Qed.
Lemma lem8131285 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term63 A B P lt2 p s) = (term64 A B P p lt2 s).
Proof. exact (MK_COMB (@lem8131284 A B P) (@lem8131283 A B P p lt2 s)). Qed.
Lemma lem8131290 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term65 A B P lt2 p) = (term66 A B P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8131285 A B P p lt2 s)). Qed.
Lemma lem8131291 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8131292 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term67 A B P lt2 p) = (term68 A B P p lt2).
Proof. exact (MK_COMB (@lem8131291 A P) (@lem8131290 A B P p lt2)). Qed.
Lemma lem8131297 {A B P : Type'} (lt2 : type1402 A) : (term69 A B P lt2) = (term70 A B P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8131292 A B P p lt2)). Qed.
Lemma lem8131298 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8131299 {A B P : Type'} (lt2 : type1402 A) : (term71 A B P lt2) = (term72 A B P lt2).
Proof. exact (MK_COMB (@lem8131298 A B P) (@lem8131297 A B P lt2)). Qed.
Lemma lem8131304 {A B P : Type'} : (term73 A B P) = (term74 A B P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8131299 A B P lt2)). Qed.
Lemma lem8131305 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8131306 {A B P : Type'} : (term75 A B P) = (term76 A B P).
Proof. exact (MK_COMB (@lem8131305 A) (@lem8131304 A B P)). Qed.
Lemma lem8131311 {A B P : Type'} : (term76 A B P) = (term75 A B P).
Proof. exact (SYM (@lem8131306 A B P)). Qed.
Lemma lem8131313 (p : Prop) : p = (term77 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8131314 {A B P : Type'} : (term76 A B P) = (term78 A B P).
Proof. exact (@lem8131313 (term76 A B P)). Qed.
Lemma lem8131315 {A B P : Type'} : (term78 A B P) = (term76 A B P).
Proof. exact (SYM (@lem8131314 A B P)). Qed.
Lemma lem8131316 {A B P : Type'} (h1 : term79 A B P) : term79 A B P.
Proof. exact (h1). Qed.
Lemma lem8131319 {A B P : Type'} (h1 : term78 A B P) : term78 A B P.
Proof. exact (h1). Qed.
Lemma lem8131320 {A B P : Type'} : term80 A B P.
Proof. exact (fun h0 : term78 A B P => @lem8131319 A B P h0). Qed.
Lemma lem8131321 {A B P : Type'} (h1 : term80 A B P) : term80 A B P.
Proof. exact (h1). Qed.
Lemma lem8131322 {A B P : Type'} (h1 : term78 A B P) : term78 A B P.
Proof. exact (h1). Qed.
Lemma lem8131323 {A B P : Type'} (h1 : term78 A B P) (h2 : term80 A B P) : term78 A B P.
Proof. exact (@lem8131321 A B P h2 (@lem8131322 A B P h1)). Qed.
Lemma lem8131324 {A B P : Type'} (h1 : term78 A B P) : term81 A B P.
Proof. exact (fun h0 : term80 A B P => @lem8131323 A B P h1 h0). Qed.
Lemma lem8131325 {A B P : Type'} (h1 : term80 A B P) : term80 A B P.
Proof. exact (h1). Qed.
Lemma lem8131326 {A B P : Type'} (h1 : term78 A B P) (h2 : term80 A B P) : term78 A B P.
Proof. exact (@lem8131324 A B P h1 (@lem8131325 A B P h2)). Qed.
Lemma lem8131327 {A B P : Type'} (h1 : term80 A B P) : term80 A B P.
Proof. exact (fun h0 : term78 A B P => @lem8131326 A B P h0 h1). Qed.
Lemma lem8131328 {A B P : Type'} : term82 A B P.
Proof. exact (fun h0 : term80 A B P => @lem8131327 A B P h0). Qed.
Lemma lem8131331 {A B P : Type'} : term80 A B P.
Proof. exact (@lem8131328 A B P (@lem8131320 A B P)). Qed.
Lemma lem8131332 {A B P : Type'} : term80 A B P.
Proof. exact (@lem8131331 A B P). Qed.
Lemma lem8131334 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8131335 {A B P : Type'} : (term78 A B P) = (term83 A B P).
Proof. exact (@lem8131334 (term79 A B P)). Qed.
Lemma lem8131337 (t : Prop) : (term84 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8131338 {A B P : Type'} : (term83 A B P) = (term76 A B P).
Proof. exact (@lem8131337 (term76 A B P)). Qed.
Lemma lem8131421 {A B P : Type'} : (term78 A B P) = (term76 A B P).
Proof. exact (TRANS (@lem8131335 A B P) (@lem8131338 A B P)). Qed.
Lemma lem8131422 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term39 A B P t f a) = (term39 A B P t g a)) = ((term39 A B P t f a) = (term39 A B P t g a)).
Proof. exact (eq_refl ((term39 A B P t f a) = (term39 A B P t g a))). Qed.
Lemma lem8131427 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term85 A B P lt2 s a f g z) = (term85 A B P lt2 s a f g z).
Proof. exact (eq_refl (term85 A B P lt2 s a f g z)). Qed.
Lemma lem8131428 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term86 A B P lt2 s a f g) = (term86 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131427 A B P lt2 s a f g z)). Qed.
Lemma lem8131429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8131430 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term87 A B P lt2 s a f g) = (term87 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8131429 A) (@lem8131428 A B P lt2 s a f g)). Qed.
Lemma lem8131433 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term88 A B P p g a) = (term88 A B P p g a).
Proof. exact (eq_refl (term88 A B P p g a)). Qed.
Lemma lem8131434 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term89 A B P p lt2 s a f g) = (term89 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131433 A B P p g a) (@lem8131430 A B P lt2 s a f g)). Qed.
Lemma lem8131437 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term88 A B P p f a) = (term88 A B P p f a).
Proof. exact (eq_refl (term88 A B P p f a)). Qed.
Lemma lem8131438 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term90 A B P p lt2 s a f g) = (term90 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131437 A B P p f a) (@lem8131434 A B P p lt2 s a f g)). Qed.
Lemma lem8131439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8131440 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term45 A B P p lt2 s a f g) = (term45 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131439) (@lem8131438 A B P p lt2 s a f g)). Qed.
Lemma lem8131441 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term47 A B P p lt2 s f t g a) = (term47 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131440 A B P p lt2 s a f g) (@lem8131422 A B P f t g a)). Qed.
Lemma lem8131442 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term49 A B P p lt2 s f t g) = (term49 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8131441 A B P p lt2 s f t g a)). Qed.
Lemma lem8131443 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131444 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term51 A B P p lt2 s f t g) = (term51 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131443 P) (@lem8131442 A B P p lt2 s f t g)). Qed.
Lemma lem8131445 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term53 A B P p lt2 s f t) = (term53 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8131444 A B P p lt2 s f t g)). Qed.
Lemma lem8131446 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131447 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term55 A B P p lt2 s f t) = (term55 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131446 A B) (@lem8131445 A B P p lt2 s f t)). Qed.
Lemma lem8131448 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term57 A B P p lt2 s t) = (term57 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131447 A B P p lt2 s f t)). Qed.
Lemma lem8131449 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131450 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term58 A B P p lt2 s t) = (term58 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131449 A B) (@lem8131448 A B P p lt2 s t)). Qed.
Lemma lem8131455 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term91 A B P p lt2 t f s a) = (term91 A B P p lt2 t f s a).
Proof. exact (eq_refl (term91 A B P p lt2 t f s a)). Qed.
Lemma lem8131456 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term92 A B P p lt2 t f s) = (term92 A B P p lt2 t f s).
Proof. exact (fun_ext (fun a : P => @lem8131455 A B P p lt2 t f s a)). Qed.
Lemma lem8131457 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131458 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term93 A B P p lt2 t f s) = (term93 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8131457 P) (@lem8131456 A B P p lt2 t f s)). Qed.
Lemma lem8131459 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term94 A B P p lt2 t s) = (term94 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8131458 A B P p lt2 t f s)). Qed.
Lemma lem8131460 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131461 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term18 A B P p lt2 t s) = (term18 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8131460 A B) (@lem8131459 A B P p lt2 t s)). Qed.
Lemma lem8131462 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8131467 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term85 A B P lt2 s a f g z) = (term85 A B P lt2 s a f g z).
Proof. exact (eq_refl (term85 A B P lt2 s a f g z)). Qed.
Lemma lem8131468 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term86 A B P lt2 s a f g) = (term86 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131467 A B P lt2 s a f g z)). Qed.
Lemma lem8131469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8131470 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term87 A B P lt2 s a f g) = (term87 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8131469 A) (@lem8131468 A B P lt2 s a f g)). Qed.
Lemma lem8131473 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term88 A B P p g a) = (term88 A B P p g a).
Proof. exact (eq_refl (term88 A B P p g a)). Qed.
Lemma lem8131474 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term89 A B P p lt2 s a f g) = (term89 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131473 A B P p g a) (@lem8131470 A B P lt2 s a f g)). Qed.
Lemma lem8131477 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term88 A B P p f a) = (term88 A B P p f a).
Proof. exact (eq_refl (term88 A B P p f a)). Qed.
Lemma lem8131478 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term90 A B P p lt2 s a f g) = (term90 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131477 A B P p f a) (@lem8131474 A B P p lt2 s a f g)). Qed.
Lemma lem8131479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8131480 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term45 A B P p lt2 s a f g) = (term45 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131479) (@lem8131478 A B P p lt2 s a f g)). Qed.
Lemma lem8131481 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term95 A B P p lt2 s f t g a) = (term95 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131480 A B P p lt2 s a f g) (@lem8131462 A B P f t g a)). Qed.
Lemma lem8131482 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term96 A B P p lt2 s f t g) = (term96 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8131481 A B P p lt2 s f t g a)). Qed.
Lemma lem8131483 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131484 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term97 A B P p lt2 s f t g) = (term97 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131483 P) (@lem8131482 A B P p lt2 s f t g)). Qed.
Lemma lem8131485 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term98 A B P p lt2 s f t) = (term98 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8131484 A B P p lt2 s f t g)). Qed.
Lemma lem8131486 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131487 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term99 A B P p lt2 s f t) = (term99 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131486 A B) (@lem8131485 A B P p lt2 s f t)). Qed.
Lemma lem8131488 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term100 A B P p lt2 s t) = (term100 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131487 A B P p lt2 s f t)). Qed.
Lemma lem8131489 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131490 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term15 A B P p lt2 s t) = (term15 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131489 A B) (@lem8131488 A B P p lt2 s t)). Qed.
Lemma lem8131491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8131492 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term17 A B P p lt2 s t) = (term17 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131491) (@lem8131490 A B P p lt2 s t)). Qed.
Lemma lem8131493 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term20 A B P p lt2 t s) = (term20 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8131492 A B P p lt2 s t) (@lem8131461 A B P p lt2 t s)). Qed.
Lemma lem8131494 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8131495 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term22 A B P p lt2 t s) = (term22 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8131494) (@lem8131493 A B P p lt2 t s)). Qed.
Lemma lem8131496 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term60 A B P p lt2 s t) = (term60 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131495 A B P p lt2 t s) (@lem8131450 A B P p lt2 s t)). Qed.
Lemma lem8131497 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term62 A B P p lt2 s) = (term62 A B P p lt2 s).
Proof. exact (fun_ext (fun t : type557 A B P => @lem8131496 A B P p lt2 s t)). Qed.
Lemma lem8131498 {A B P : Type'} : (@all ((A -> B) -> P -> A)) = (@all ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> A))). Qed.
Lemma lem8131499 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term64 A B P p lt2 s) = (term64 A B P p lt2 s).
Proof. exact (MK_COMB (@lem8131498 A B P) (@lem8131497 A B P p lt2 s)). Qed.
Lemma lem8131500 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term66 A B P p lt2) = (term66 A B P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8131499 A B P p lt2 s)). Qed.
Lemma lem8131501 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8131502 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term68 A B P p lt2) = (term68 A B P p lt2).
Proof. exact (MK_COMB (@lem8131501 A P) (@lem8131500 A B P p lt2)). Qed.
Lemma lem8131503 {A B P : Type'} (lt2 : type1402 A) : (term70 A B P lt2) = (term70 A B P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8131502 A B P p lt2)). Qed.
Lemma lem8131504 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8131505 {A B P : Type'} (lt2 : type1402 A) : (term72 A B P lt2) = (term72 A B P lt2).
Proof. exact (MK_COMB (@lem8131504 A B P) (@lem8131503 A B P lt2)). Qed.
Lemma lem8131506 {A B P : Type'} : (term74 A B P) = (term74 A B P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8131505 A B P lt2)). Qed.
Lemma lem8131507 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8131508 {A B P : Type'} : (term76 A B P) = (term76 A B P).
Proof. exact (MK_COMB (@lem8131507 A) (@lem8131506 A B P)). Qed.
Lemma lem8131617 {A B P : Type'} : (term78 A B P) = (term76 A B P).
Proof. exact (TRANS (@lem8131421 A B P) (@lem8131508 A B P)). Qed.
Lemma lem8131618 {A B P : Type'} : (term76 A B P) = (term78 A B P).
Proof. exact (SYM (@lem8131617 A B P)). Qed.
Lemma lem8131619 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term20 A B P p lt2 t s) : term20 A B P p lt2 t s.
Proof. exact (h1). Qed.
Lemma lem8131620 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term90 A B P p lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8131622 (p : Prop) : p = (term77 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8131623 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term39 A B P t f a) = (term39 A B P t g a)) = (term101 A B P f t g a).
Proof. exact (@lem8131622 ((term39 A B P t f a) = (term39 A B P t g a))). Qed.
Lemma lem8131624 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term101 A B P f t g a) = ((term39 A B P t f a) = (term39 A B P t g a)).
Proof. exact (SYM (@lem8131623 A B P f t g a)). Qed.
Lemma lem8131625 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (h1 : term102 A B P f t g a) : term102 A B P f t g a.
Proof. exact (h1). Qed.
Lemma lem8131634 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term103 A B P lt2 s a f g z) = (term104 A B P lt2 s a f g z).
Proof. exact (@lem17362 (term105 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8131635 {A : Type'} (P : A -> Prop) : (term106 A P) = (term107 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8131636 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term108 A B P lt2 s a f g) = (term109 A B P lt2 s a f g).
Proof. exact (@lem8131635 A (term86 A B P lt2 s a f g)). Qed.
Lemma lem8131637 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term110 A B P lt2 s a f g z) = (term85 A B P lt2 s a f g z).
Proof. exact (eq_refl (term110 A B P lt2 s a f g z)). Qed.
Lemma lem8131638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8131639 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term111 A B P lt2 s a f g z) = (term103 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8131638) (@lem8131637 A B P lt2 s a f g z)). Qed.
Lemma lem8131640 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term111 A B P lt2 s a f g z) = (term104 A B P lt2 s a f g z).
Proof. exact (TRANS (@lem8131639 A B P lt2 s a f g z) (@lem8131634 A B P lt2 s a f g z)). Qed.
Lemma lem8131641 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term112 A B P lt2 s a f g) = (term113 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131640 A B P lt2 s a f g z)). Qed.
Lemma lem8131642 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131643 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term109 A B P lt2 s a f g) = (term114 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8131642 A) (@lem8131641 A B P lt2 s a f g)). Qed.
Lemma lem8131644 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term108 A B P lt2 s a f g) = (term114 A B P lt2 s a f g).
Proof. exact (TRANS (@lem8131636 A B P lt2 s a f g) (@lem8131643 A B P lt2 s a f g)). Qed.
Lemma lem8131646 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term115 A B P p g a) = (term115 A B P p g a).
Proof. exact (eq_refl (term115 A B P p g a)). Qed.
Lemma lem8131647 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term116 A B P p lt2 s a f g) = (term117 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131646 A B P p g a) (@lem8131644 A B P lt2 s a f g)). Qed.
Lemma lem8131648 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term118 A B P p lt2 s a f g) = (term116 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p g a) (term87 A B P lt2 s a f g)). Qed.
Lemma lem8131649 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term118 A B P p lt2 s a f g) = (term117 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8131648 A B P p lt2 s a f g) (@lem8131647 A B P p lt2 s a f g)). Qed.
Lemma lem8131651 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term115 A B P p f a) = (term115 A B P p f a).
Proof. exact (eq_refl (term115 A B P p f a)). Qed.
Lemma lem8131652 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term119 A B P p lt2 s a f g) = (term120 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131651 A B P p f a) (@lem8131649 A B P p lt2 s a f g)). Qed.
Lemma lem8131653 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term121 A B P p lt2 s a f g) = (term119 A B P p lt2 s a f g).
Proof. exact (@lem17045 (p f a) (term89 A B P p lt2 s a f g)). Qed.
Lemma lem8131654 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term121 A B P p lt2 s a f g) = (term120 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8131653 A B P p lt2 s a f g) (@lem8131652 A B P p lt2 s a f g)). Qed.
Lemma lem8131655 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8131656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8131657 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term122 A B P p lt2 s a f g) = (term123 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131656) (@lem8131654 A B P p lt2 s a f g)). Qed.
Lemma lem8131658 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term124 A B P p lt2 s f t g a) = (term125 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131657 A B P p lt2 s a f g) (@lem8131655 A B P f t g a)). Qed.
Lemma lem8131659 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term95 A B P p lt2 s f t g a) = (term124 A B P p lt2 s f t g a).
Proof. exact (@lem17265 (term90 A B P p lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8131660 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term95 A B P p lt2 s f t g a) = (term125 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8131659 A B P p lt2 s f t g a) (@lem8131658 A B P p lt2 s f t g a)). Qed.
Lemma lem8131661 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term96 A B P p lt2 s f t g) = (term126 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8131660 A B P p lt2 s f t g a)). Qed.
Lemma lem8131662 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131663 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term97 A B P p lt2 s f t g) = (term127 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131662 P) (@lem8131661 A B P p lt2 s f t g)). Qed.
Lemma lem8131664 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term98 A B P p lt2 s f t) = (term128 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8131663 A B P p lt2 s f t g)). Qed.
Lemma lem8131665 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131666 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term99 A B P p lt2 s f t) = (term129 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131665 A B) (@lem8131664 A B P p lt2 s f t)). Qed.
Lemma lem8131667 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term100 A B P p lt2 s t) = (term130 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131666 A B P p lt2 s f t)). Qed.
Lemma lem8131668 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131669 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term15 A B P p lt2 s t) = (term131 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131668 A B) (@lem8131667 A B P p lt2 s t)). Qed.
Lemma lem8131676 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term91 A B P p lt2 t f s a) = (term132 A B P p lt2 t f s a).
Proof. exact (@lem17265 (p f a) (term133 A B P lt2 t f s a)). Qed.
Lemma lem8131677 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term92 A B P p lt2 t f s) = (term134 A B P p lt2 t f s).
Proof. exact (fun_ext (fun a : P => @lem8131676 A B P p lt2 t f s a)). Qed.
Lemma lem8131678 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131679 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term93 A B P p lt2 t f s) = (term135 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8131678 P) (@lem8131677 A B P p lt2 t f s)). Qed.
Lemma lem8131680 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term94 A B P p lt2 t s) = (term136 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8131679 A B P p lt2 t f s)). Qed.
Lemma lem8131681 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131682 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term18 A B P p lt2 t s) = (term137 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8131681 A B) (@lem8131680 A B P p lt2 t s)). Qed.
Lemma lem8131683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8131684 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term17 A B P p lt2 s t) = (term138 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131683) (@lem8131669 A B P p lt2 s t)). Qed.
Lemma lem8131685 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term20 A B P p lt2 t s) = (term139 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8131684 A B P p lt2 s t) (@lem8131682 A B P p lt2 t s)). Qed.
Lemma lem8131844 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8131845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (@lem8131844 A P Q). Qed.
Lemma lem8131846 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term142 A B P p lt2 s a f g) = (term143 A B P p lt2 s a f g).
Proof. exact (@lem8131845 A (term144 A B P p g a) (term113 A B P lt2 s a f g)). Qed.
Lemma lem8131847 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term145 A B P lt2 s a f g z) = (term104 A B P lt2 s a f g z).
Proof. exact (eq_refl (term145 A B P lt2 s a f g z)). Qed.
Lemma lem8131848 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term146 A B P lt2 s a f g) = (term113 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131847 A B P lt2 s a f g z)). Qed.
Lemma lem8131849 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131850 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term147 A B P lt2 s a f g) = (term114 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8131849 A) (@lem8131848 A B P lt2 s a f g)). Qed.
Lemma lem8131851 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term115 A B P p g a) = (term115 A B P p g a).
Proof. exact (eq_refl (term115 A B P p g a)). Qed.
Lemma lem8131852 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term142 A B P p lt2 s a f g) = (term117 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131851 A B P p g a) (@lem8131850 A B P lt2 s a f g)). Qed.
Lemma lem8131853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8131854 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term148 A B P p lt2 s a f g) = (term149 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131853) (@lem8131852 A B P p lt2 s a f g)). Qed.
Lemma lem8131855 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term145 A B P lt2 s a f g z) = (term104 A B P lt2 s a f g z).
Proof. exact (eq_refl (term145 A B P lt2 s a f g z)). Qed.
Lemma lem8131856 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term115 A B P p g a) = (term115 A B P p g a).
Proof. exact (eq_refl (term115 A B P p g a)). Qed.
Lemma lem8131857 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term150 A B P p lt2 s a f g z) = (term151 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8131856 A B P p g a) (@lem8131855 A B P lt2 s a f g z)). Qed.
Lemma lem8131858 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term152 A B P p lt2 s a f g) = (term153 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131857 A B P p lt2 s a f g z)). Qed.
Lemma lem8131859 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131860 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term143 A B P p lt2 s a f g) = (term154 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131859 A) (@lem8131858 A B P p lt2 s a f g)). Qed.
Lemma lem8131861 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term142 A B P p lt2 s a f g) = (term143 A B P p lt2 s a f g)) = ((term117 A B P p lt2 s a f g) = (term154 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8131854 A B P p lt2 s a f g) (@lem8131860 A B P p lt2 s a f g)). Qed.
Lemma lem8131862 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term117 A B P p lt2 s a f g) = (term154 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8131861 A B P p lt2 s a f g) (@lem8131846 A B P p lt2 s a f g)). Qed.
Lemma lem8131863 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term115 A B P p f a) = (term115 A B P p f a).
Proof. exact (eq_refl (term115 A B P p f a)). Qed.
Lemma lem8131864 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term120 A B P p lt2 s a f g) = (term155 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131863 A B P p f a) (@lem8131862 A B P p lt2 s a f g)). Qed.
Lemma lem8131866 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8131867 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (@lem8131866 A P Q). Qed.
Lemma lem8131868 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term156 A B P p lt2 s a f g) = (term157 A B P p lt2 s a f g).
Proof. exact (@lem8131867 A (term144 A B P p f a) (term153 A B P p lt2 s a f g)). Qed.
Lemma lem8131869 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term158 A B P p lt2 s a f g z) = (term151 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term158 A B P p lt2 s a f g z)). Qed.
Lemma lem8131870 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term159 A B P p lt2 s a f g) = (term153 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131869 A B P p lt2 s a f g z)). Qed.
Lemma lem8131871 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131872 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term160 A B P p lt2 s a f g) = (term154 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131871 A) (@lem8131870 A B P p lt2 s a f g)). Qed.
Lemma lem8131873 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term115 A B P p f a) = (term115 A B P p f a).
Proof. exact (eq_refl (term115 A B P p f a)). Qed.
Lemma lem8131874 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term156 A B P p lt2 s a f g) = (term155 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131873 A B P p f a) (@lem8131872 A B P p lt2 s a f g)). Qed.
Lemma lem8131875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8131876 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term161 A B P p lt2 s a f g) = (term162 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131875) (@lem8131874 A B P p lt2 s a f g)). Qed.
Lemma lem8131877 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term158 A B P p lt2 s a f g z) = (term151 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term158 A B P p lt2 s a f g z)). Qed.
Lemma lem8131878 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term115 A B P p f a) = (term115 A B P p f a).
Proof. exact (eq_refl (term115 A B P p f a)). Qed.
Lemma lem8131879 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term163 A B P p lt2 s a f g z) = (term164 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8131878 A B P p f a) (@lem8131877 A B P p lt2 s a f g z)). Qed.
Lemma lem8131880 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term165 A B P p lt2 s a f g) = (term166 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131879 A B P p lt2 s a f g z)). Qed.
Lemma lem8131881 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131882 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term157 A B P p lt2 s a f g) = (term167 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131881 A) (@lem8131880 A B P p lt2 s a f g)). Qed.
Lemma lem8131883 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : ((term156 A B P p lt2 s a f g) = (term157 A B P p lt2 s a f g)) = ((term155 A B P p lt2 s a f g) = (term167 A B P p lt2 s a f g)).
Proof. exact (MK_COMB (@lem8131876 A B P p lt2 s a f g) (@lem8131882 A B P p lt2 s a f g)). Qed.
Lemma lem8131884 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term155 A B P p lt2 s a f g) = (term167 A B P p lt2 s a f g).
Proof. exact (EQ_MP (@lem8131883 A B P p lt2 s a f g) (@lem8131868 A B P p lt2 s a f g)). Qed.
Lemma lem8131885 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term120 A B P p lt2 s a f g) = (term167 A B P p lt2 s a f g).
Proof. exact (TRANS (@lem8131864 A B P p lt2 s a f g) (@lem8131884 A B P p lt2 s a f g)). Qed.
Lemma lem8131886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8131887 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term123 A B P p lt2 s a f g) = (term168 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131886) (@lem8131885 A B P p lt2 s a f g)). Qed.
Lemma lem8131888 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8131889 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term125 A B P p lt2 s f t g a) = (term169 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131887 A B P p lt2 s a f g) (@lem8131888 A B P f t g a)). Qed.
Lemma lem8131891 {A : Type'} (P : A -> Prop) (Q : Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8131892 {A : Type'} (P : A -> Prop) (Q : Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (@lem8131891 A P Q). Qed.
Lemma lem8131893 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term172 A B P p lt2 s f t g a) = (term173 A B P p lt2 s f t g a).
Proof. exact (@lem8131892 A (term166 A B P p lt2 s a f g) ((t f a) = (t g a))). Qed.
Lemma lem8131894 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term174 A B P p lt2 s a f g z) = (term164 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term174 A B P p lt2 s a f g z)). Qed.
Lemma lem8131895 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term175 A B P p lt2 s a f g) = (term166 A B P p lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8131894 A B P p lt2 s a f g z)). Qed.
Lemma lem8131896 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131897 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term176 A B P p lt2 s a f g) = (term167 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131896 A) (@lem8131895 A B P p lt2 s a f g)). Qed.
Lemma lem8131898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8131899 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term177 A B P p lt2 s a f g) = (term168 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8131898) (@lem8131897 A B P p lt2 s a f g)). Qed.
Lemma lem8131900 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8131901 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term172 A B P p lt2 s f t g a) = (term169 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131899 A B P p lt2 s a f g) (@lem8131900 A B P f t g a)). Qed.
Lemma lem8131902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8131903 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term178 A B P p lt2 s f t g a) = (term179 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131902) (@lem8131901 A B P p lt2 s f t g a)). Qed.
Lemma lem8131904 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term174 A B P p lt2 s a f g z) = (term164 A B P p lt2 s a f g z).
Proof. exact (eq_refl (term174 A B P p lt2 s a f g z)). Qed.
Lemma lem8131905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8131906 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term180 A B P p lt2 s a f g z) = (term181 A B P p lt2 s a f g z).
Proof. exact (MK_COMB (@lem8131905) (@lem8131904 A B P p lt2 s a f g z)). Qed.
Lemma lem8131907 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((t f a) = (t g a)).
Proof. exact (eq_refl ((t f a) = (t g a))). Qed.
Lemma lem8131908 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term182 A B P p lt2 s z f t g a) = (term183 A B P p lt2 s z f t g a).
Proof. exact (MK_COMB (@lem8131906 A B P p lt2 s a f g z) (@lem8131907 A B P f t g a)). Qed.
Lemma lem8131909 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term184 A B P p lt2 s f t g a) = (term185 A B P p lt2 s f t g a).
Proof. exact (fun_ext (fun z : A => @lem8131908 A B P p lt2 s z f t g a)). Qed.
Lemma lem8131910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131911 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term173 A B P p lt2 s f t g a) = (term186 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131910 A) (@lem8131909 A B P p lt2 s f t g a)). Qed.
Lemma lem8131912 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term172 A B P p lt2 s f t g a) = (term173 A B P p lt2 s f t g a)) = ((term169 A B P p lt2 s f t g a) = (term186 A B P p lt2 s f t g a)).
Proof. exact (MK_COMB (@lem8131903 A B P p lt2 s f t g a) (@lem8131911 A B P p lt2 s f t g a)). Qed.
Lemma lem8131913 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term169 A B P p lt2 s f t g a) = (term186 A B P p lt2 s f t g a).
Proof. exact (EQ_MP (@lem8131912 A B P p lt2 s f t g a) (@lem8131893 A B P p lt2 s f t g a)). Qed.
Lemma lem8131914 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term125 A B P p lt2 s f t g a) = (term186 A B P p lt2 s f t g a).
Proof. exact (TRANS (@lem8131889 A B P p lt2 s f t g a) (@lem8131913 A B P p lt2 s f t g a)). Qed.
Lemma lem8131915 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term126 A B P p lt2 s f t g) = (term187 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8131914 A B P p lt2 s f t g a)). Qed.
Lemma lem8131916 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131917 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term127 A B P p lt2 s f t g) = (term188 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131916 P) (@lem8131915 A B P p lt2 s f t g)). Qed.
Lemma lem8131919 {A B : Type'} (P : type1413 A B) : (term189 A B P) = (term190 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8131920 {A P : Type'} (P' : type1470 A P) : (term191 A P P') = (term192 A P P').
Proof. exact (@lem8131919 P A P'). Qed.
Lemma lem8131921 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term193 A B P p lt2 s f t g) = (term194 A B P p lt2 s f t g).
Proof. exact (@lem8131920 A P (term195 A B P p lt2 s f t g)). Qed.
Lemma lem8131922 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term196 A B P p lt2 s f t g a) = (term185 A B P p lt2 s f t g a).
Proof. exact (eq_refl (term196 A B P p lt2 s f t g a)). Qed.
Lemma lem8131923 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8131924 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (z : A) : (term197 A B P p lt2 s f t g a z) = (term198 A B P p lt2 s f t g a z).
Proof. exact (MK_COMB (@lem8131922 A B P p lt2 s f t g a) (@lem8131923 A z)). Qed.
Lemma lem8131925 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term198 A B P p lt2 s f t g a z) = (term183 A B P p lt2 s z f t g a).
Proof. exact (eq_refl (term198 A B P p lt2 s f t g a z)). Qed.
Lemma lem8131926 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term197 A B P p lt2 s f t g a z) = (term183 A B P p lt2 s z f t g a).
Proof. exact (TRANS (@lem8131924 A B P p lt2 s f t g a z) (@lem8131925 A B P p lt2 s z f t g a)). Qed.
Lemma lem8131927 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term199 A B P p lt2 s f t g a) = (term185 A B P p lt2 s f t g a).
Proof. exact (fun_ext (fun z : A => @lem8131926 A B P p lt2 s z f t g a)). Qed.
Lemma lem8131928 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8131929 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term200 A B P p lt2 s f t g a) = (term186 A B P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8131928 A) (@lem8131927 A B P p lt2 s f t g a)). Qed.
Lemma lem8131930 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term201 A B P p lt2 s f t g) = (term187 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8131929 A B P p lt2 s f t g a)). Qed.
Lemma lem8131931 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131932 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term193 A B P p lt2 s f t g) = (term188 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131931 P) (@lem8131930 A B P p lt2 s f t g)). Qed.
Lemma lem8131933 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8131934 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term202 A B P p lt2 s f t g) = (term203 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131933) (@lem8131932 A B P p lt2 s f t g)). Qed.
Lemma lem8131935 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term196 A B P p lt2 s f t g a) = (term185 A B P p lt2 s f t g a).
Proof. exact (eq_refl (term196 A B P p lt2 s f t g a)). Qed.
Lemma lem8131936 {A P : Type'} (z : P -> A) (a : P) : (z a) = (z a).
Proof. exact (eq_refl (z a)). Qed.
Lemma lem8131937 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (z : P -> A) (a : P) : (term204 A B P p lt2 s f t g z a) = (term205 A B P p lt2 s f t g z a).
Proof. exact (MK_COMB (@lem8131935 A B P p lt2 s f t g a) (@lem8131936 A P z a)). Qed.
Lemma lem8131938 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term205 A B P p lt2 s f t g z a) = (term206 A B P p lt2 s z f t g a).
Proof. exact (eq_refl (term205 A B P p lt2 s f t g z a)). Qed.
Lemma lem8131939 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term204 A B P p lt2 s f t g z a) = (term206 A B P p lt2 s z f t g a).
Proof. exact (TRANS (@lem8131937 A B P p lt2 s f t g z a) (@lem8131938 A B P p lt2 s z f t g a)). Qed.
Lemma lem8131940 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term207 A B P p lt2 s f t g z) = (term208 A B P p lt2 s z f t g).
Proof. exact (fun_ext (fun a : P => @lem8131939 A B P p lt2 s z f t g a)). Qed.
Lemma lem8131941 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8131942 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term209 A B P p lt2 s f t g z) = (term210 A B P p lt2 s z f t g).
Proof. exact (MK_COMB (@lem8131941 P) (@lem8131940 A B P p lt2 s z f t g)). Qed.
Lemma lem8131943 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term211 A B P p lt2 s f t g) = (term212 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun z : P -> A => @lem8131942 A B P p lt2 s z f t g)). Qed.
Lemma lem8131944 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8131945 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term194 A B P p lt2 s f t g) = (term213 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131944 A P) (@lem8131943 A B P p lt2 s f t g)). Qed.
Lemma lem8131946 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : ((term193 A B P p lt2 s f t g) = (term194 A B P p lt2 s f t g)) = ((term188 A B P p lt2 s f t g) = (term213 A B P p lt2 s f t g)).
Proof. exact (MK_COMB (@lem8131934 A B P p lt2 s f t g) (@lem8131945 A B P p lt2 s f t g)). Qed.
Lemma lem8131947 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term188 A B P p lt2 s f t g) = (term213 A B P p lt2 s f t g).
Proof. exact (EQ_MP (@lem8131946 A B P p lt2 s f t g) (@lem8131921 A B P p lt2 s f t g)). Qed.
Lemma lem8131948 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term127 A B P p lt2 s f t g) = (term213 A B P p lt2 s f t g).
Proof. exact (TRANS (@lem8131917 A B P p lt2 s f t g) (@lem8131947 A B P p lt2 s f t g)). Qed.
Lemma lem8131949 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term128 A B P p lt2 s f t) = (term214 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8131948 A B P p lt2 s f t g)). Qed.
Lemma lem8131950 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131951 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term129 A B P p lt2 s f t) = (term215 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131950 A B) (@lem8131949 A B P p lt2 s f t)). Qed.
Lemma lem8131953 {A B : Type'} (P : type1413 A B) : (term189 A B P) = (term190 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8131954 {A B P : Type'} (P' : type537 A B P) : (term216 A B P P') = (term217 A B P P').
Proof. exact (@lem8131953 (A -> B) (P -> A) P'). Qed.
Lemma lem8131955 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term218 A B P p lt2 s f t) = (term219 A B P p lt2 s f t).
Proof. exact (@lem8131954 A B P (term220 A B P p lt2 s f t)). Qed.
Lemma lem8131956 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term221 A B P p lt2 s f t g) = (term212 A B P p lt2 s f t g).
Proof. exact (eq_refl (term221 A B P p lt2 s f t g)). Qed.
Lemma lem8131957 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8131958 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) (z : P -> A) : (term222 A B P p lt2 s f t g z) = (term223 A B P p lt2 s f t g z).
Proof. exact (MK_COMB (@lem8131956 A B P p lt2 s f t g) (@lem8131957 A P z)). Qed.
Lemma lem8131959 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term223 A B P p lt2 s f t g z) = (term210 A B P p lt2 s z f t g).
Proof. exact (eq_refl (term223 A B P p lt2 s f t g z)). Qed.
Lemma lem8131960 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term222 A B P p lt2 s f t g z) = (term210 A B P p lt2 s z f t g).
Proof. exact (TRANS (@lem8131958 A B P p lt2 s f t g z) (@lem8131959 A B P p lt2 s z f t g)). Qed.
Lemma lem8131961 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term224 A B P p lt2 s f t g) = (term212 A B P p lt2 s f t g).
Proof. exact (fun_ext (fun z : P -> A => @lem8131960 A B P p lt2 s z f t g)). Qed.
Lemma lem8131962 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8131963 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term225 A B P p lt2 s f t g) = (term213 A B P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8131962 A P) (@lem8131961 A B P p lt2 s f t g)). Qed.
Lemma lem8131964 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term226 A B P p lt2 s f t) = (term214 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8131963 A B P p lt2 s f t g)). Qed.
Lemma lem8131965 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131966 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term218 A B P p lt2 s f t) = (term215 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131965 A B) (@lem8131964 A B P p lt2 s f t)). Qed.
Lemma lem8131967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8131968 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term227 A B P p lt2 s f t) = (term228 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131967) (@lem8131966 A B P p lt2 s f t)). Qed.
Lemma lem8131969 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term221 A B P p lt2 s f t g) = (term212 A B P p lt2 s f t g).
Proof. exact (eq_refl (term221 A B P p lt2 s f t g)). Qed.
Lemma lem8131970 {A B P : Type'} (z : type557 A B P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8131971 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (z : type557 A B P) (g : A -> B) : (term229 A B P p lt2 s f t z g) = (term230 A B P p lt2 s f t z g).
Proof. exact (MK_COMB (@lem8131969 A B P p lt2 s f t g) (@lem8131970 A B P z g)). Qed.
Lemma lem8131972 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term230 A B P p lt2 s f t z g) = (term231 A B P p lt2 s z f t g).
Proof. exact (eq_refl (term230 A B P p lt2 s f t z g)). Qed.
Lemma lem8131973 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term229 A B P p lt2 s f t z g) = (term231 A B P p lt2 s z f t g).
Proof. exact (TRANS (@lem8131971 A B P p lt2 s f t z g) (@lem8131972 A B P p lt2 s z f t g)). Qed.
Lemma lem8131974 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term232 A B P p lt2 s f t z) = (term233 A B P p lt2 s z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8131973 A B P p lt2 s z f t g)). Qed.
Lemma lem8131975 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131976 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term234 A B P p lt2 s f t z) = (term235 A B P p lt2 s z f t).
Proof. exact (MK_COMB (@lem8131975 A B) (@lem8131974 A B P p lt2 s z f t)). Qed.
Lemma lem8131977 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term236 A B P p lt2 s f t) = (term237 A B P p lt2 s f t).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8131976 A B P p lt2 s z f t)). Qed.
Lemma lem8131978 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8131979 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term219 A B P p lt2 s f t) = (term238 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131978 A B P) (@lem8131977 A B P p lt2 s f t)). Qed.
Lemma lem8131980 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : ((term218 A B P p lt2 s f t) = (term219 A B P p lt2 s f t)) = ((term215 A B P p lt2 s f t) = (term238 A B P p lt2 s f t)).
Proof. exact (MK_COMB (@lem8131968 A B P p lt2 s f t) (@lem8131979 A B P p lt2 s f t)). Qed.
Lemma lem8131981 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term215 A B P p lt2 s f t) = (term238 A B P p lt2 s f t).
Proof. exact (EQ_MP (@lem8131980 A B P p lt2 s f t) (@lem8131955 A B P p lt2 s f t)). Qed.
Lemma lem8131982 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term129 A B P p lt2 s f t) = (term238 A B P p lt2 s f t).
Proof. exact (TRANS (@lem8131951 A B P p lt2 s f t) (@lem8131981 A B P p lt2 s f t)). Qed.
Lemma lem8131983 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term130 A B P p lt2 s t) = (term239 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131982 A B P p lt2 s f t)). Qed.
Lemma lem8131984 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8131985 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term131 A B P p lt2 s t) = (term240 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131984 A B) (@lem8131983 A B P p lt2 s t)). Qed.
Lemma lem8131987 {A B : Type'} (P : type1413 A B) : (term189 A B P) = (term190 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8131988 {A B P : Type'} (P' : type495 A B P) : (term241 A B P P') = (term242 A B P P').
Proof. exact (@lem8131987 (A -> B) (type557 A B P) P'). Qed.
Lemma lem8131989 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term243 A B P p lt2 s t) = (term244 A B P p lt2 s t).
Proof. exact (@lem8131988 A B P (term245 A B P p lt2 s t)). Qed.
Lemma lem8131990 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term246 A B P p lt2 s t f) = (term237 A B P p lt2 s f t).
Proof. exact (eq_refl (term246 A B P p lt2 s t f)). Qed.
Lemma lem8131991 {A B P : Type'} (z : type557 A B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8131992 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) (z : type557 A B P) : (term247 A B P p lt2 s t f z) = (term248 A B P p lt2 s f t z).
Proof. exact (MK_COMB (@lem8131990 A B P p lt2 s f t) (@lem8131991 A B P z)). Qed.
Lemma lem8131993 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term248 A B P p lt2 s f t z) = (term235 A B P p lt2 s z f t).
Proof. exact (eq_refl (term248 A B P p lt2 s f t z)). Qed.
Lemma lem8131994 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type557 A B P) (f : A -> B) (t : type557 A B P) : (term247 A B P p lt2 s t f z) = (term235 A B P p lt2 s z f t).
Proof. exact (TRANS (@lem8131992 A B P p lt2 s f t z) (@lem8131993 A B P p lt2 s z f t)). Qed.
Lemma lem8131995 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term249 A B P p lt2 s t f) = (term237 A B P p lt2 s f t).
Proof. exact (fun_ext (fun z : type557 A B P => @lem8131994 A B P p lt2 s z f t)). Qed.
Lemma lem8131996 {A B P : Type'} : (@ex ((A -> B) -> P -> A)) = (@ex ((A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> P -> A))). Qed.
Lemma lem8131997 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term250 A B P p lt2 s t f) = (term238 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8131996 A B P) (@lem8131995 A B P p lt2 s f t)). Qed.
Lemma lem8131998 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term251 A B P p lt2 s t) = (term239 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8131997 A B P p lt2 s f t)). Qed.
Lemma lem8131999 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132000 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term243 A B P p lt2 s t) = (term240 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8131999 A B) (@lem8131998 A B P p lt2 s t)). Qed.
Lemma lem8132001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8132002 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term252 A B P p lt2 s t) = (term253 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8132001) (@lem8132000 A B P p lt2 s t)). Qed.
Lemma lem8132003 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type557 A B P) : (term246 A B P p lt2 s t f) = (term237 A B P p lt2 s f t).
Proof. exact (eq_refl (term246 A B P p lt2 s t f)). Qed.
Lemma lem8132004 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8132005 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) (z : type518 A B P) (f : A -> B) : (term254 A B P p lt2 s t z f) = (term255 A B P p lt2 s t z f).
Proof. exact (MK_COMB (@lem8132003 A B P p lt2 s f t) (@lem8132004 A B P z f)). Qed.
Lemma lem8132006 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term255 A B P p lt2 s t z f) = (term256 A B P p lt2 s z f t).
Proof. exact (eq_refl (term255 A B P p lt2 s t z f)). Qed.
Lemma lem8132007 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term254 A B P p lt2 s t z f) = (term256 A B P p lt2 s z f t).
Proof. exact (TRANS (@lem8132005 A B P p lt2 s t z f) (@lem8132006 A B P p lt2 s z f t)). Qed.
Lemma lem8132008 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term257 A B P p lt2 s t z) = (term258 A B P p lt2 s z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8132007 A B P p lt2 s z f t)). Qed.
Lemma lem8132009 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132010 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term259 A B P p lt2 s t z) = (term260 A B P p lt2 s z t).
Proof. exact (MK_COMB (@lem8132009 A B) (@lem8132008 A B P p lt2 s z t)). Qed.
Lemma lem8132011 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term261 A B P p lt2 s t) = (term262 A B P p lt2 s t).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8132010 A B P p lt2 s z t)). Qed.
Lemma lem8132012 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8132013 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term244 A B P p lt2 s t) = (term263 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8132012 A B P) (@lem8132011 A B P p lt2 s t)). Qed.
Lemma lem8132014 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : ((term243 A B P p lt2 s t) = (term244 A B P p lt2 s t)) = ((term240 A B P p lt2 s t) = (term263 A B P p lt2 s t)).
Proof. exact (MK_COMB (@lem8132002 A B P p lt2 s t) (@lem8132013 A B P p lt2 s t)). Qed.
Lemma lem8132015 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term240 A B P p lt2 s t) = (term263 A B P p lt2 s t).
Proof. exact (EQ_MP (@lem8132014 A B P p lt2 s t) (@lem8131989 A B P p lt2 s t)). Qed.
Lemma lem8132016 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term131 A B P p lt2 s t) = (term263 A B P p lt2 s t).
Proof. exact (TRANS (@lem8131985 A B P p lt2 s t) (@lem8132015 A B P p lt2 s t)). Qed.
Lemma lem8132017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8132018 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term138 A B P p lt2 s t) = (term264 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8132017) (@lem8132016 A B P p lt2 s t)). Qed.
Lemma lem8132019 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term137 A B P p lt2 t s) = (term137 A B P p lt2 t s).
Proof. exact (eq_refl (term137 A B P p lt2 t s)). Qed.
Lemma lem8132020 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term139 A B P p lt2 t s) = (term265 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8132018 A B P p lt2 s t) (@lem8132019 A B P p lt2 t s)). Qed.
Lemma lem8132022 {A : Type'} (P : A -> Prop) (Q : Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8132023 {A B P : Type'} (P' : type96 A B P) (Q : Prop) : (term268 A B P P' Q) = (term269 A B P P' Q).
Proof. exact (@lem8132022 (type518 A B P) P' Q). Qed.
Lemma lem8132024 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term270 A B P p lt2 t s) = (term271 A B P p lt2 t s).
Proof. exact (@lem8132023 A B P (term262 A B P p lt2 s t) (term137 A B P p lt2 t s)). Qed.
Lemma lem8132025 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term272 A B P p lt2 s t z) = (term260 A B P p lt2 s z t).
Proof. exact (eq_refl (term272 A B P p lt2 s t z)). Qed.
Lemma lem8132026 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term273 A B P p lt2 s t) = (term262 A B P p lt2 s t).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8132025 A B P p lt2 s z t)). Qed.
Lemma lem8132027 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8132028 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term274 A B P p lt2 s t) = (term263 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8132027 A B P) (@lem8132026 A B P p lt2 s t)). Qed.
Lemma lem8132029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8132030 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : (term275 A B P p lt2 s t) = (term264 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8132029) (@lem8132028 A B P p lt2 s t)). Qed.
Lemma lem8132031 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term137 A B P p lt2 t s) = (term137 A B P p lt2 t s).
Proof. exact (eq_refl (term137 A B P p lt2 t s)). Qed.
Lemma lem8132032 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term270 A B P p lt2 t s) = (term265 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8132030 A B P p lt2 s t) (@lem8132031 A B P p lt2 t s)). Qed.
Lemma lem8132033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8132034 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term276 A B P p lt2 t s) = (term277 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8132033) (@lem8132032 A B P p lt2 t s)). Qed.
Lemma lem8132035 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term272 A B P p lt2 s t z) = (term260 A B P p lt2 s z t).
Proof. exact (eq_refl (term272 A B P p lt2 s t z)). Qed.
Lemma lem8132036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8132037 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term278 A B P p lt2 s t z) = (term279 A B P p lt2 s z t).
Proof. exact (MK_COMB (@lem8132036) (@lem8132035 A B P p lt2 s z t)). Qed.
Lemma lem8132038 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term137 A B P p lt2 t s) = (term137 A B P p lt2 t s).
Proof. exact (eq_refl (term137 A B P p lt2 t s)). Qed.
Lemma lem8132039 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term280 A B P z p lt2 t s) = (term281 A B P z p lt2 t s).
Proof. exact (MK_COMB (@lem8132037 A B P p lt2 s z t) (@lem8132038 A B P p lt2 t s)). Qed.
Lemma lem8132040 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term282 A B P p lt2 t s) = (term283 A B P p lt2 t s).
Proof. exact (fun_ext (fun z : type518 A B P => @lem8132039 A B P z p lt2 t s)). Qed.
Lemma lem8132041 {A B P : Type'} : (@ex ((A -> B) -> (A -> B) -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> P -> A))). Qed.
Lemma lem8132042 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term271 A B P p lt2 t s) = (term284 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8132041 A B P) (@lem8132040 A B P p lt2 t s)). Qed.
Lemma lem8132043 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : ((term270 A B P p lt2 t s) = (term271 A B P p lt2 t s)) = ((term265 A B P p lt2 t s) = (term284 A B P p lt2 t s)).
Proof. exact (MK_COMB (@lem8132034 A B P p lt2 t s) (@lem8132042 A B P p lt2 t s)). Qed.
Lemma lem8132044 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term265 A B P p lt2 t s) = (term284 A B P p lt2 t s).
Proof. exact (EQ_MP (@lem8132043 A B P p lt2 t s) (@lem8132024 A B P p lt2 t s)). Qed.
Lemma lem8132046 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term139 A B P p lt2 t s) = (term284 A B P p lt2 t s).
Proof. exact (TRANS (@lem8132020 A B P p lt2 t s) (@lem8132044 A B P p lt2 t s)). Qed.
Lemma lem8132047 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term20 A B P p lt2 t s) = (term284 A B P p lt2 t s).
Proof. exact (TRANS (@lem8131685 A B P p lt2 t s) (@lem8132046 A B P p lt2 t s)). Qed.
Lemma lem8132048 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term20 A B P p lt2 t s) : term284 A B P p lt2 t s.
Proof. exact (EQ_MP (@lem8132047 A B P p lt2 t s) (@lem8131619 A B P p lt2 t s h1)). Qed.
Lemma lem8132057 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term85 A B P lt2 s a f g z) = (term285 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term105 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8132058 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term86 A B P lt2 s a f g) = (term286 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8132057 A B P lt2 s a f g z)). Qed.
Lemma lem8132059 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8132060 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term87 A B P lt2 s a f g) = (term287 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8132059 A) (@lem8132058 A B P lt2 s a f g)). Qed.
Lemma lem8132062 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term88 A B P p g a) = (term88 A B P p g a).
Proof. exact (eq_refl (term88 A B P p g a)). Qed.
Lemma lem8132063 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term89 A B P p lt2 s a f g) = (term288 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8132062 A B P p g a) (@lem8132060 A B P lt2 s a f g)). Qed.
Lemma lem8132065 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term88 A B P p f a) = (term88 A B P p f a).
Proof. exact (eq_refl (term88 A B P p f a)). Qed.
Lemma lem8132118 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term90 A B P p lt2 s a f g) = (term289 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8132065 A B P p f a) (@lem8132063 A B P p lt2 s a f g)). Qed.
Lemma lem8132119 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term289 A B P p lt2 s a f g.
Proof. exact (EQ_MP (@lem8132118 A B P p lt2 s a f g) (@lem8131620 A B P p lt2 s a f g h1)). Qed.
Lemma lem8132125 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (h1 : term102 A B P f t g a) : term102 A B P f t g a.
Proof. exact (h1). Qed.
Lemma lem8132126 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term281 A B P z p lt2 t s.
Proof. exact (h1). Qed.
Lemma lem8132127 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8132132 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8132132 A B f x). Qed.
Lemma lem8132135 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8132133 A B f z). Qed.
Lemma lem8132140 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8132140 A B f x). Qed.
Lemma lem8132143 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8132141 A B g z). Qed.
Lemma lem8132144 {A B : Type'} (f : A -> B) (z : A) : (term290 A B f z) = (term291 A B f z).
Proof. exact (MK_COMB (@lem8132127 B) (@lem8132135 A B f z)). Qed.
Lemma lem8132145 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8132144 A B f z) (@lem8132143 A B g z)). Qed.
Lemma lem8132146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8132153 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132154 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132153 P A f x). Qed.
Lemma lem8132156 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8132154 A P s a). Qed.
Lemma lem8132157 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8132158 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term105 A P lt2 z s a) = (term292 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8132157 A lt2 z) (@lem8132156 A P s a)). Qed.
Lemma lem8132160 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132161 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8132160 A (A -> Prop) f x). Qed.
Lemma lem8132162 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8132161 A lt2 z). Qed.
Lemma lem8132163 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8132164 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term292 A P lt2 z s a) = (term293 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8132162 A lt2 z) (@lem8132163 A P s a)). Qed.
Lemma lem8132166 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132167 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8132166 A Prop f x). Qed.
Lemma lem8132168 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term293 A P lt2 z s a) = (term294 A P lt2 z s a).
Proof. exact (@lem8132167 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a)). Qed.
Lemma lem8132169 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term292 A P lt2 z s a) = (term294 A P lt2 z s a).
Proof. exact (TRANS (@lem8132164 A P lt2 z s a) (@lem8132168 A P lt2 z s a)). Qed.
Lemma lem8132170 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term105 A P lt2 z s a) = (term294 A P lt2 z s a).
Proof. exact (TRANS (@lem8132158 A P lt2 z s a) (@lem8132169 A P lt2 z s a)). Qed.
Lemma lem8132171 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term295 A P lt2 z s a) = (term296 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8132146) (@lem8132170 A P lt2 z s a)). Qed.
Lemma lem8132172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8132173 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term297 A P lt2 z s a) = (term298 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8132172) (@lem8132171 A P lt2 z s a)). Qed.
Lemma lem8132174 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term285 A B P lt2 s a f g z) = (term299 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8132173 A P lt2 z s a) (@lem8132145 A B f g z)). Qed.
Lemma lem8132175 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term286 A B P lt2 s a f g) = (term300 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8132174 A B P lt2 s a f g z)). Qed.
Lemma lem8132176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8132177 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term287 A B P lt2 s a f g) = (term301 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8132176 A) (@lem8132175 A B P lt2 s a f g)). Qed.
Lemma lem8132184 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132185 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8132184 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8132186 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8132185 A B P p g). Qed.
Lemma lem8132187 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132188 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8132186 A B P p g) (@lem8132187 P a)). Qed.
Lemma lem8132190 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132191 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8132190 P Prop f x). Qed.
Lemma lem8132192 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term302 A B P p g a).
Proof. exact (@lem8132191 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8132194 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term302 A B P p g a).
Proof. exact (TRANS (@lem8132188 A B P p g a) (@lem8132192 A B P p g a)). Qed.
Lemma lem8132195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8132196 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term88 A B P p g a) = (term303 A B P p g a).
Proof. exact (MK_COMB (@lem8132195) (@lem8132194 A B P p g a)). Qed.
Lemma lem8132197 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term288 A B P p lt2 s a f g) = (term304 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8132196 A B P p g a) (@lem8132177 A B P lt2 s a f g)). Qed.
Lemma lem8132204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132205 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8132204 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8132206 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8132205 A B P p f). Qed.
Lemma lem8132207 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132208 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8132206 A B P p f) (@lem8132207 P a)). Qed.
Lemma lem8132210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132211 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8132210 P Prop f x). Qed.
Lemma lem8132212 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term302 A B P p f a).
Proof. exact (@lem8132211 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8132214 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term302 A B P p f a).
Proof. exact (TRANS (@lem8132208 A B P p f a) (@lem8132212 A B P p f a)). Qed.
Lemma lem8132215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8132216 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term88 A B P p f a) = (term303 A B P p f a).
Proof. exact (MK_COMB (@lem8132215) (@lem8132214 A B P p f a)). Qed.
Lemma lem8132217 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term289 A B P p lt2 s a f g) = (term305 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8132216 A B P p f a) (@lem8132197 A B P p lt2 s a f g)). Qed.
Lemma lem8132218 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term305 A B P p lt2 s a f g.
Proof. exact (EQ_MP (@lem8132217 A B P p lt2 s a f g) (@lem8132119 A B P p lt2 s a f g h1)). Qed.
Lemma lem8132219 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8132220 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8132221 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8132228 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132229 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132228 (A -> B) (P -> A) f x). Qed.
Lemma lem8132230 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8132229 A B P t f). Qed.
Lemma lem8132231 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132232 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> A) t f a).
Proof. exact (MK_COMB (@lem8132230 A B P t f) (@lem8132231 P a)). Qed.
Lemma lem8132234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132235 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132234 P A f x). Qed.
Lemma lem8132236 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t f a) = (term306 A B P t f a).
Proof. exact (@lem8132235 A P (@I ((A -> B) -> P -> A) t f) a). Qed.
Lemma lem8132238 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (term306 A B P t f a).
Proof. exact (TRANS (@lem8132232 A B P t f a) (@lem8132236 A B P t f a)). Qed.
Lemma lem8132239 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term39 A B P t f a) = (term307 A B P t f a).
Proof. exact (MK_COMB (@lem8132221 A B f) (@lem8132238 A B P t f a)). Qed.
Lemma lem8132241 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8132241 A B f x). Qed.
Lemma lem8132243 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term307 A B P t f a) = (term308 A B P t f a).
Proof. exact (@lem8132242 A B f (term306 A B P t f a)). Qed.
Lemma lem8132244 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term39 A B P t f a) = (term308 A B P t f a).
Proof. exact (TRANS (@lem8132239 A B P t f a) (@lem8132243 A B P t f a)). Qed.
Lemma lem8132245 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8132252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132253 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132252 (A -> B) (P -> A) f x). Qed.
Lemma lem8132254 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> A) t g).
Proof. exact (@lem8132253 A B P t g). Qed.
Lemma lem8132255 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132256 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (@I ((A -> B) -> P -> A) t g a).
Proof. exact (MK_COMB (@lem8132254 A B P t g) (@lem8132255 P a)). Qed.
Lemma lem8132258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132259 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132258 P A f x). Qed.
Lemma lem8132260 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t g a) = (term306 A B P t g a).
Proof. exact (@lem8132259 A P (@I ((A -> B) -> P -> A) t g) a). Qed.
Lemma lem8132262 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (term306 A B P t g a).
Proof. exact (TRANS (@lem8132256 A B P t g a) (@lem8132260 A B P t g a)). Qed.
Lemma lem8132263 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term39 A B P t g a) = (term307 A B P t g a).
Proof. exact (MK_COMB (@lem8132245 A B g) (@lem8132262 A B P t g a)). Qed.
Lemma lem8132265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132266 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8132265 A B f x). Qed.
Lemma lem8132267 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term307 A B P t g a) = (term308 A B P t g a).
Proof. exact (@lem8132266 A B g (term306 A B P t g a)). Qed.
Lemma lem8132268 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (term39 A B P t g a) = (term308 A B P t g a).
Proof. exact (TRANS (@lem8132263 A B P t g a) (@lem8132267 A B P t g a)). Qed.
Lemma lem8132269 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term44 A B P t f a) = (term309 A B P t f a).
Proof. exact (MK_COMB (@lem8132220 B) (@lem8132244 A B P t f a)). Qed.
Lemma lem8132270 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term39 A B P t f a) = (term39 A B P t g a)) = ((term308 A B P t f a) = (term308 A B P t g a)).
Proof. exact (MK_COMB (@lem8132269 A B P t f a) (@lem8132268 A B P t g a)). Qed.
Lemma lem8132271 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term102 A B P f t g a) = (term310 A B P f t g a).
Proof. exact (MK_COMB (@lem8132219) (@lem8132270 A B P f t g a)). Qed.
Lemma lem8132273 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8132280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132281 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132280 (A -> B) (P -> A) f x). Qed.
Lemma lem8132282 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8132281 A B P t f). Qed.
Lemma lem8132283 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132284 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> A) t f a).
Proof. exact (MK_COMB (@lem8132282 A B P t f) (@lem8132283 P a)). Qed.
Lemma lem8132286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132287 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132286 P A f x). Qed.
Lemma lem8132288 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t f a) = (term306 A B P t f a).
Proof. exact (@lem8132287 A P (@I ((A -> B) -> P -> A) t f) a). Qed.
Lemma lem8132290 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (term306 A B P t f a).
Proof. exact (TRANS (@lem8132284 A B P t f a) (@lem8132288 A B P t f a)). Qed.
Lemma lem8132295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132296 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132295 P A f x). Qed.
Lemma lem8132298 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8132296 A P s a). Qed.
Lemma lem8132299 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (a : P) : (term311 A B P lt2 t f a) = (term312 A B P lt2 t f a).
Proof. exact (MK_COMB (@lem8132273 A lt2) (@lem8132290 A B P t f a)). Qed.
Lemma lem8132300 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term133 A B P lt2 t f s a) = (term313 A B P lt2 t f s a).
Proof. exact (MK_COMB (@lem8132299 A B P lt2 t f a) (@lem8132298 A P s a)). Qed.
Lemma lem8132302 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132303 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8132302 A (A -> Prop) f x). Qed.
Lemma lem8132304 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (a : P) : (term312 A B P lt2 t f a) = (term314 A B P lt2 t f a).
Proof. exact (@lem8132303 A lt2 (term306 A B P t f a)). Qed.
Lemma lem8132305 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8132306 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term313 A B P lt2 t f s a) = (term315 A B P lt2 t f s a).
Proof. exact (MK_COMB (@lem8132304 A B P lt2 t f a) (@lem8132305 A P s a)). Qed.
Lemma lem8132308 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132309 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8132308 A Prop f x). Qed.
Lemma lem8132310 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term315 A B P lt2 t f s a) = (term316 A B P lt2 t f s a).
Proof. exact (@lem8132309 A (term314 A B P lt2 t f a) (@I (P -> A) s a)). Qed.
Lemma lem8132311 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term313 A B P lt2 t f s a) = (term316 A B P lt2 t f s a).
Proof. exact (TRANS (@lem8132306 A B P lt2 t f s a) (@lem8132310 A B P lt2 t f s a)). Qed.
Lemma lem8132312 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term133 A B P lt2 t f s a) = (term316 A B P lt2 t f s a).
Proof. exact (TRANS (@lem8132300 A B P lt2 t f s a) (@lem8132311 A B P lt2 t f s a)). Qed.
Lemma lem8132313 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8132320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132321 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8132320 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8132322 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8132321 A B P p f). Qed.
Lemma lem8132323 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132324 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8132322 A B P p f) (@lem8132323 P a)). Qed.
Lemma lem8132326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132327 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8132326 P Prop f x). Qed.
Lemma lem8132328 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term302 A B P p f a).
Proof. exact (@lem8132327 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8132330 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term302 A B P p f a).
Proof. exact (TRANS (@lem8132324 A B P p f a) (@lem8132328 A B P p f a)). Qed.
Lemma lem8132331 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term144 A B P p f a) = (term317 A B P p f a).
Proof. exact (MK_COMB (@lem8132313) (@lem8132330 A B P p f a)). Qed.
Lemma lem8132332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8132333 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term115 A B P p f a) = (term318 A B P p f a).
Proof. exact (MK_COMB (@lem8132332) (@lem8132331 A B P p f a)). Qed.
Lemma lem8132334 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term132 A B P p lt2 t f s a) = (term319 A B P p lt2 t f s a).
Proof. exact (MK_COMB (@lem8132333 A B P p f a) (@lem8132312 A B P lt2 t f s a)). Qed.
Lemma lem8132335 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term134 A B P p lt2 t f s) = (term320 A B P p lt2 t f s).
Proof. exact (fun_ext (fun a : P => @lem8132334 A B P p lt2 t f s a)). Qed.
Lemma lem8132336 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8132337 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term135 A B P p lt2 t f s) = (term321 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8132336 P) (@lem8132335 A B P p lt2 t f s)). Qed.
Lemma lem8132338 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term136 A B P p lt2 t s) = (term322 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8132337 A B P p lt2 t f s)). Qed.
Lemma lem8132339 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132340 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term137 A B P p lt2 t s) = (term323 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8132339 A B) (@lem8132338 A B P p lt2 t s)). Qed.
Lemma lem8132341 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8132348 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132349 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132348 (A -> B) (P -> A) f x). Qed.
Lemma lem8132350 {A B P : Type'} (t : type557 A B P) (f : A -> B) : (t f) = (@I ((A -> B) -> P -> A) t f).
Proof. exact (@lem8132349 A B P t f). Qed.
Lemma lem8132351 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132352 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (@I ((A -> B) -> P -> A) t f a).
Proof. exact (MK_COMB (@lem8132350 A B P t f) (@lem8132351 P a)). Qed.
Lemma lem8132354 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132355 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132354 P A f x). Qed.
Lemma lem8132356 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t f a) = (term306 A B P t f a).
Proof. exact (@lem8132355 A P (@I ((A -> B) -> P -> A) t f) a). Qed.
Lemma lem8132358 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (t f a) = (term306 A B P t f a).
Proof. exact (TRANS (@lem8132352 A B P t f a) (@lem8132356 A B P t f a)). Qed.
Lemma lem8132365 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132366 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132365 (A -> B) (P -> A) f x). Qed.
Lemma lem8132367 {A B P : Type'} (t : type557 A B P) (g : A -> B) : (t g) = (@I ((A -> B) -> P -> A) t g).
Proof. exact (@lem8132366 A B P t g). Qed.
Lemma lem8132368 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132369 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (@I ((A -> B) -> P -> A) t g a).
Proof. exact (MK_COMB (@lem8132367 A B P t g) (@lem8132368 P a)). Qed.
Lemma lem8132371 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132372 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132371 P A f x). Qed.
Lemma lem8132373 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> A) t g a) = (term306 A B P t g a).
Proof. exact (@lem8132372 A P (@I ((A -> B) -> P -> A) t g) a). Qed.
Lemma lem8132375 {A B P : Type'} (t : type557 A B P) (g : A -> B) (a : P) : (t g a) = (term306 A B P t g a).
Proof. exact (TRANS (@lem8132369 A B P t g a) (@lem8132373 A B P t g a)). Qed.
Lemma lem8132376 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term324 A B P t f a) = (term325 A B P t f a).
Proof. exact (MK_COMB (@lem8132341 A) (@lem8132358 A B P t f a)). Qed.
Lemma lem8132377 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((t f a) = (t g a)) = ((term306 A B P t f a) = (term306 A B P t g a)).
Proof. exact (MK_COMB (@lem8132376 A B P t f a) (@lem8132375 A B P t g a)). Qed.
Lemma lem8132378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8132379 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8132380 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8132389 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132390 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8132389 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8132391 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8132390 A B P z f). Qed.
Lemma lem8132392 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8132393 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8132391 A B P z f) (@lem8132392 A B g)). Qed.
Lemma lem8132395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132396 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132395 (A -> B) (P -> A) f x). Qed.
Lemma lem8132397 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term326 A B P z f g).
Proof. exact (@lem8132396 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8132398 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term326 A B P z f g).
Proof. exact (TRANS (@lem8132393 A B P z f g) (@lem8132397 A B P z f g)). Qed.
Lemma lem8132399 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132400 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term327 A B P z f g a).
Proof. exact (MK_COMB (@lem8132398 A B P z f g) (@lem8132399 P a)). Qed.
Lemma lem8132402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132403 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132402 P A f x). Qed.
Lemma lem8132404 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term327 A B P z f g a) = (term328 A B P z f g a).
Proof. exact (@lem8132403 A P (term326 A B P z f g) a). Qed.
Lemma lem8132406 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term328 A B P z f g a).
Proof. exact (TRANS (@lem8132400 A B P z f g a) (@lem8132404 A B P z f g a)). Qed.
Lemma lem8132407 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term329 A B P z f g a) = (term330 A B P z f g a).
Proof. exact (MK_COMB (@lem8132380 A B f) (@lem8132406 A B P z f g a)). Qed.
Lemma lem8132409 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8132409 A B f x). Qed.
Lemma lem8132411 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term330 A B P z f g a) = (term331 A B P z f g a).
Proof. exact (@lem8132410 A B f (term328 A B P z f g a)). Qed.
Lemma lem8132412 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term329 A B P z f g a) = (term331 A B P z f g a).
Proof. exact (TRANS (@lem8132407 A B P z f g a) (@lem8132411 A B P z f g a)). Qed.
Lemma lem8132413 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8132422 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132423 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8132422 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8132424 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8132423 A B P z f). Qed.
Lemma lem8132425 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8132426 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8132424 A B P z f) (@lem8132425 A B g)). Qed.
Lemma lem8132428 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132429 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132428 (A -> B) (P -> A) f x). Qed.
Lemma lem8132430 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term326 A B P z f g).
Proof. exact (@lem8132429 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8132431 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term326 A B P z f g).
Proof. exact (TRANS (@lem8132426 A B P z f g) (@lem8132430 A B P z f g)). Qed.
Lemma lem8132432 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132433 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term327 A B P z f g a).
Proof. exact (MK_COMB (@lem8132431 A B P z f g) (@lem8132432 P a)). Qed.
Lemma lem8132435 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132436 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132435 P A f x). Qed.
Lemma lem8132437 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term327 A B P z f g a) = (term328 A B P z f g a).
Proof. exact (@lem8132436 A P (term326 A B P z f g) a). Qed.
Lemma lem8132439 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term328 A B P z f g a).
Proof. exact (TRANS (@lem8132433 A B P z f g a) (@lem8132437 A B P z f g a)). Qed.
Lemma lem8132440 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term332 A B P z f g a) = (term333 A B P z f g a).
Proof. exact (MK_COMB (@lem8132413 A B g) (@lem8132439 A B P z f g a)). Qed.
Lemma lem8132442 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132443 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8132442 A B f x). Qed.
Lemma lem8132444 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term333 A B P z f g a) = (term334 A B P z f g a).
Proof. exact (@lem8132443 A B g (term328 A B P z f g a)). Qed.
Lemma lem8132445 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term332 A B P z f g a) = (term334 A B P z f g a).
Proof. exact (TRANS (@lem8132440 A B P z f g a) (@lem8132444 A B P z f g a)). Qed.
Lemma lem8132446 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term335 A B P z f g a) = (term336 A B P z f g a).
Proof. exact (MK_COMB (@lem8132379 B) (@lem8132412 A B P z f g a)). Qed.
Lemma lem8132447 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : ((term329 A B P z f g a) = (term332 A B P z f g a)) = ((term331 A B P z f g a) = (term334 A B P z f g a)).
Proof. exact (MK_COMB (@lem8132446 A B P z f g a) (@lem8132445 A B P z f g a)). Qed.
Lemma lem8132448 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term337 A B P z f g a) = (term338 A B P z f g a).
Proof. exact (MK_COMB (@lem8132378) (@lem8132447 A B P z f g a)). Qed.
Lemma lem8132449 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8132458 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132459 {A B P : Type'} (f : type518 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> P -> A) f x).
Proof. exact (@lem8132458 (A -> B) (type557 A B P) f x). Qed.
Lemma lem8132460 {A B P : Type'} (z : type518 A B P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> P -> A) z f).
Proof. exact (@lem8132459 A B P z f). Qed.
Lemma lem8132461 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8132462 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8132460 A B P z f) (@lem8132461 A B g)). Qed.
Lemma lem8132464 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132465 {A B P : Type'} (f : type557 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> A) f x).
Proof. exact (@lem8132464 (A -> B) (P -> A) f x). Qed.
Lemma lem8132466 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> P -> A) z f g) = (term326 A B P z f g).
Proof. exact (@lem8132465 A B P (@I ((A -> B) -> (A -> B) -> P -> A) z f) g). Qed.
Lemma lem8132467 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) : (z f g) = (term326 A B P z f g).
Proof. exact (TRANS (@lem8132462 A B P z f g) (@lem8132466 A B P z f g)). Qed.
Lemma lem8132468 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132469 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term327 A B P z f g a).
Proof. exact (MK_COMB (@lem8132467 A B P z f g) (@lem8132468 P a)). Qed.
Lemma lem8132471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132472 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132471 P A f x). Qed.
Lemma lem8132473 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term327 A B P z f g a) = (term328 A B P z f g a).
Proof. exact (@lem8132472 A P (term326 A B P z f g) a). Qed.
Lemma lem8132475 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (z f g a) = (term328 A B P z f g a).
Proof. exact (TRANS (@lem8132469 A B P z f g a) (@lem8132473 A B P z f g a)). Qed.
Lemma lem8132480 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132481 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8132480 P A f x). Qed.
Lemma lem8132483 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8132481 A P s a). Qed.
Lemma lem8132484 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term339 A B P lt2 z f g a) = (term340 A B P lt2 z f g a).
Proof. exact (MK_COMB (@lem8132449 A lt2) (@lem8132475 A B P z f g a)). Qed.
Lemma lem8132485 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term341 A B P lt2 z f g s a) = (term342 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8132484 A B P lt2 z f g a) (@lem8132483 A P s a)). Qed.
Lemma lem8132487 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132488 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8132487 A (A -> Prop) f x). Qed.
Lemma lem8132489 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term340 A B P lt2 z f g a) = (term343 A B P lt2 z f g a).
Proof. exact (@lem8132488 A lt2 (term328 A B P z f g a)). Qed.
Lemma lem8132490 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8132491 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term342 A B P lt2 z f g s a) = (term344 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8132489 A B P lt2 z f g a) (@lem8132490 A P s a)). Qed.
Lemma lem8132493 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132494 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8132493 A Prop f x). Qed.
Lemma lem8132495 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term344 A B P lt2 z f g s a) = (term345 A B P lt2 z f g s a).
Proof. exact (@lem8132494 A (term343 A B P lt2 z f g a) (@I (P -> A) s a)). Qed.
Lemma lem8132496 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term342 A B P lt2 z f g s a) = (term345 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8132491 A B P lt2 z f g s a) (@lem8132495 A B P lt2 z f g s a)). Qed.
Lemma lem8132497 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term341 A B P lt2 z f g s a) = (term345 A B P lt2 z f g s a).
Proof. exact (TRANS (@lem8132485 A B P lt2 z f g s a) (@lem8132496 A B P lt2 z f g s a)). Qed.
Lemma lem8132498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8132499 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term346 A B P lt2 z f g s a) = (term347 A B P lt2 z f g s a).
Proof. exact (MK_COMB (@lem8132498) (@lem8132497 A B P lt2 z f g s a)). Qed.
Lemma lem8132500 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term348 A B P lt2 s z f g a) = (term349 A B P lt2 s z f g a).
Proof. exact (MK_COMB (@lem8132499 A B P lt2 z f g s a) (@lem8132448 A B P z f g a)). Qed.
Lemma lem8132501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8132508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132509 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8132508 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8132510 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8132509 A B P p g). Qed.
Lemma lem8132511 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132512 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8132510 A B P p g) (@lem8132511 P a)). Qed.
Lemma lem8132514 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132515 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8132514 P Prop f x). Qed.
Lemma lem8132516 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term302 A B P p g a).
Proof. exact (@lem8132515 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8132518 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term302 A B P p g a).
Proof. exact (TRANS (@lem8132512 A B P p g a) (@lem8132516 A B P p g a)). Qed.
Lemma lem8132519 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term144 A B P p g a) = (term317 A B P p g a).
Proof. exact (MK_COMB (@lem8132501) (@lem8132518 A B P p g a)). Qed.
Lemma lem8132520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8132521 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term115 A B P p g a) = (term318 A B P p g a).
Proof. exact (MK_COMB (@lem8132520) (@lem8132519 A B P p g a)). Qed.
Lemma lem8132522 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term350 A B P p lt2 s z f g a) = (term351 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8132521 A B P p g a) (@lem8132500 A B P lt2 s z f g a)). Qed.
Lemma lem8132523 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8132530 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132531 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8132530 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8132532 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8132531 A B P p f). Qed.
Lemma lem8132533 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8132534 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8132532 A B P p f) (@lem8132533 P a)). Qed.
Lemma lem8132536 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8132537 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8132536 P Prop f x). Qed.
Lemma lem8132538 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term302 A B P p f a).
Proof. exact (@lem8132537 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8132540 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term302 A B P p f a).
Proof. exact (TRANS (@lem8132534 A B P p f a) (@lem8132538 A B P p f a)). Qed.
Lemma lem8132541 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term144 A B P p f a) = (term317 A B P p f a).
Proof. exact (MK_COMB (@lem8132523) (@lem8132540 A B P p f a)). Qed.
Lemma lem8132542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8132543 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term115 A B P p f a) = (term318 A B P p f a).
Proof. exact (MK_COMB (@lem8132542) (@lem8132541 A B P p f a)). Qed.
Lemma lem8132544 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term352 A B P p lt2 s z f g a) = (term353 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8132543 A B P p f a) (@lem8132522 A B P p lt2 s z f g a)). Qed.
Lemma lem8132545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8132546 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term354 A B P p lt2 s z f g a) = (term355 A B P p lt2 s z f g a).
Proof. exact (MK_COMB (@lem8132545) (@lem8132544 A B P p lt2 s z f g a)). Qed.
Lemma lem8132547 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term356 A B P p lt2 s z f t g a) = (term357 A B P p lt2 s z f t g a).
Proof. exact (MK_COMB (@lem8132546 A B P p lt2 s z f g a) (@lem8132377 A B P f t g a)). Qed.
Lemma lem8132548 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term358 A B P p lt2 s z f t g) = (term359 A B P p lt2 s z f t g).
Proof. exact (fun_ext (fun a : P => @lem8132547 A B P p lt2 s z f t g a)). Qed.
Lemma lem8132549 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8132550 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term360 A B P p lt2 s z f t g) = (term361 A B P p lt2 s z f t g).
Proof. exact (MK_COMB (@lem8132549 P) (@lem8132548 A B P p lt2 s z f t g)). Qed.
Lemma lem8132551 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term362 A B P p lt2 s z f t) = (term363 A B P p lt2 s z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8132550 A B P p lt2 s z f t g)). Qed.
Lemma lem8132552 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132553 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term256 A B P p lt2 s z f t) = (term364 A B P p lt2 s z f t).
Proof. exact (MK_COMB (@lem8132552 A B) (@lem8132551 A B P p lt2 s z f t)). Qed.
Lemma lem8132554 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term258 A B P p lt2 s z t) = (term365 A B P p lt2 s z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8132553 A B P p lt2 s z f t)). Qed.
Lemma lem8132555 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132556 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term260 A B P p lt2 s z t) = (term366 A B P p lt2 s z t).
Proof. exact (MK_COMB (@lem8132555 A B) (@lem8132554 A B P p lt2 s z t)). Qed.
Lemma lem8132557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8132558 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type518 A B P) (t : type557 A B P) : (term279 A B P p lt2 s z t) = (term367 A B P p lt2 s z t).
Proof. exact (MK_COMB (@lem8132557) (@lem8132556 A B P p lt2 s z t)). Qed.
Lemma lem8132559 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term281 A B P z p lt2 t s) = (term368 A B P z p lt2 t s).
Proof. exact (MK_COMB (@lem8132558 A B P p lt2 s z t) (@lem8132340 A B P p lt2 t s)). Qed.
Lemma lem8132560 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term368 A B P z p lt2 t s.
Proof. exact (EQ_MP (@lem8132559 A B P z p lt2 t s) (@lem8132126 A B P z p lt2 t s h1)). Qed.
Lemma lem8132561 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term323 A B P p lt2 t s.
Proof. exact (proj2 (@lem8132560 A B P z p lt2 t s h1)). Qed.
Lemma lem8132562 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term366 A B P p lt2 s z t.
Proof. exact (proj1 (@lem8132560 A B P z p lt2 t s h1)). Qed.
Lemma lem8132563 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term304 A B P p lt2 s a f g.
Proof. exact (proj2 (@lem8132218 A B P p lt2 s a f g h1)). Qed.
Lemma lem8132565 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term301 A B P lt2 s a f g.
Proof. exact (proj2 (@lem8132563 A B P p lt2 s a f g h1)). Qed.
Lemma lem8132572 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : ((term306 A B P t f a) = (term306 A B P t g a)) = ((term306 A B P t f a) = (term306 A B P t g a)).
Proof. exact (eq_refl ((term306 A B P t f a) = (term306 A B P t g a))). Qed.
Lemma lem8132589 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term351 A B P p lt2 s z f g a) = (term369 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term345 A B P lt2 z f g s a) (term317 A B P p g a) (term338 A B P z f g a)). Qed.
Lemma lem8132592 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term318 A B P p f a) = (term318 A B P p f a).
Proof. exact (eq_refl (term318 A B P p f a)). Qed.
Lemma lem8132593 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term353 A B P p lt2 s z f g a) = (term370 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8132592 A B P p f a) (@lem8132589 A B P lt2 s p z f g a)). Qed.
Lemma lem8132600 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term370 A B P lt2 s p z f g a) = (term371 A B P lt2 s p z f g a).
Proof. exact (@lem19490 (term372 A B P p lt2 z f g s a) (term317 A B P p f a) (term373 A B P p z f g a)). Qed.
Lemma lem8132601 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term353 A B P p lt2 s z f g a) = (term371 A B P lt2 s p z f g a).
Proof. exact (TRANS (@lem8132593 A B P lt2 s p z f g a) (@lem8132600 A B P lt2 s p z f g a)). Qed.
Lemma lem8132602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8132603 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term355 A B P p lt2 s z f g a) = (term374 A B P lt2 s p z f g a).
Proof. exact (MK_COMB (@lem8132602) (@lem8132601 A B P lt2 s p z f g a)). Qed.
Lemma lem8132604 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term357 A B P p lt2 s z f t g a) = (term375 A B P lt2 s p z f t g a).
Proof. exact (MK_COMB (@lem8132603 A B P lt2 s p z f g a) (@lem8132572 A B P f t g a)). Qed.
Lemma lem8132611 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term375 A B P lt2 s p z f t g a) = (term376 A B P lt2 s p z f t g a).
Proof. exact (@lem19699 (term377 A B P p lt2 z f g s a) (term378 A B P p z f g a) ((term306 A B P t f a) = (term306 A B P t g a))). Qed.
Lemma lem8132612 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term357 A B P p lt2 s z f t g a) = (term376 A B P lt2 s p z f t g a).
Proof. exact (TRANS (@lem8132604 A B P lt2 s p z f t g a) (@lem8132611 A B P lt2 s p z f t g a)). Qed.
Lemma lem8132613 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term359 A B P p lt2 s z f t g) = (term379 A B P lt2 s p z f t g).
Proof. exact (fun_ext (fun a : P => @lem8132612 A B P lt2 s p z f t g a)). Qed.
Lemma lem8132614 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8132615 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (t : type557 A B P) (g : A -> B) : (term361 A B P p lt2 s z f t g) = (term380 A B P lt2 s p z f t g).
Proof. exact (MK_COMB (@lem8132614 P) (@lem8132613 A B P lt2 s p z f t g)). Qed.
Lemma lem8132616 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term363 A B P p lt2 s z f t) = (term381 A B P lt2 s p z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8132615 A B P lt2 s p z f t g)). Qed.
Lemma lem8132617 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132618 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (f : A -> B) (t : type557 A B P) : (term364 A B P p lt2 s z f t) = (term382 A B P lt2 s p z f t).
Proof. exact (MK_COMB (@lem8132617 A B) (@lem8132616 A B P lt2 s p z f t)). Qed.
Lemma lem8132619 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (t : type557 A B P) : (term365 A B P p lt2 s z t) = (term383 A B P lt2 s p z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8132618 A B P lt2 s p z f t)). Qed.
Lemma lem8132620 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132622 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (t : type557 A B P) : (term366 A B P p lt2 s z t) = (term384 A B P lt2 s p z t).
Proof. exact (MK_COMB (@lem8132620 A B) (@lem8132619 A B P lt2 s p z t)). Qed.
Lemma lem8132623 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term384 A B P lt2 s p z t.
Proof. exact (EQ_MP (@lem8132622 A B P lt2 s p z t) (@lem8132562 A B P z p lt2 t s h1)). Qed.
Lemma lem8132631 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term319 A B P p lt2 t f s a) = (term319 A B P p lt2 t f s a).
Proof. exact (eq_refl (term319 A B P p lt2 t f s a)). Qed.
Lemma lem8132632 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term320 A B P p lt2 t f s) = (term320 A B P p lt2 t f s).
Proof. exact (fun_ext (fun a : P => @lem8132631 A B P p lt2 t f s a)). Qed.
Lemma lem8132633 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8132634 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) : (term321 A B P p lt2 t f s) = (term321 A B P p lt2 t f s).
Proof. exact (MK_COMB (@lem8132633 P) (@lem8132632 A B P p lt2 t f s)). Qed.
Lemma lem8132635 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term322 A B P p lt2 t s) = (term322 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8132634 A B P p lt2 t f s)). Qed.
Lemma lem8132636 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8132638 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) : (term323 A B P p lt2 t s) = (term323 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8132636 A B) (@lem8132635 A B P p lt2 t s)). Qed.
Lemma lem8132639 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term323 A B P p lt2 t s.
Proof. exact (EQ_MP (@lem8132638 A B P p lt2 t s) (@lem8132561 A B P z p lt2 t s h1)). Qed.
Lemma lem8132655 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term299 A B P lt2 s a f g z) = (term299 A B P lt2 s a f g z).
Proof. exact (eq_refl (term299 A B P lt2 s a f g z)). Qed.
Lemma lem8132656 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term300 A B P lt2 s a f g) = (term300 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8132655 A B P lt2 s a f g z)). Qed.
Lemma lem8132657 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8132659 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term301 A B P lt2 s a f g) = (term301 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8132657 A) (@lem8132656 A B P lt2 s a f g)). Qed.
Lemma lem8132660 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term301 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8132659 A B P lt2 s a f g) (@lem8132565 A B P p lt2 s a f g h1)). Qed.
Lemma lem8132661 {A B P : Type'} (_107726 : A -> B) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term385 A B P lt2 s p z t _107726.
Proof. exact (@lem8132623 A B P z p lt2 t s h1 _107726). Qed.
Lemma lem8132662 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) : (term385 A B P lt2 s p z t _107726) = (term382 A B P lt2 s p z _107726 t).
Proof. exact (eq_refl (term385 A B P lt2 s p z t _107726)). Qed.
Lemma lem8132663 {A B P : Type'} (_107726 : A -> B) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term382 A B P lt2 s p z _107726 t.
Proof. exact (EQ_MP (@lem8132662 A B P lt2 s p z _107726 t) (@lem8132661 A B P _107726 z p lt2 t s h1)). Qed.
Lemma lem8132664 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term386 A B P lt2 s p z _107726 t _107727.
Proof. exact (@lem8132663 A B P _107726 z p lt2 t s h1 _107727). Qed.
Lemma lem8132665 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) : (term386 A B P lt2 s p z _107726 t _107727) = (term380 A B P lt2 s p z _107726 t _107727).
Proof. exact (eq_refl (term386 A B P lt2 s p z _107726 t _107727)). Qed.
Lemma lem8132666 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term380 A B P lt2 s p z _107726 t _107727.
Proof. exact (EQ_MP (@lem8132665 A B P lt2 s p z _107726 t _107727) (@lem8132664 A B P _107726 _107727 z p lt2 t s h1)). Qed.
Lemma lem8132667 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term387 A B P lt2 s p z _107726 t _107727 _107728.
Proof. exact (@lem8132666 A B P _107726 _107727 z p lt2 t s h1 _107728). Qed.
Lemma lem8132668 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term387 A B P lt2 s p z _107726 t _107727 _107728) = (term376 A B P lt2 s p z _107726 t _107727 _107728).
Proof. exact (eq_refl (term387 A B P lt2 s p z _107726 t _107727 _107728)). Qed.
Lemma lem8132669 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term376 A B P lt2 s p z _107726 t _107727 _107728.
Proof. exact (EQ_MP (@lem8132668 A B P lt2 s p z _107726 t _107727 _107728) (@lem8132667 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8132670 {A B P : Type'} (_107729 : A -> B) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term388 A B P p lt2 t s _107729.
Proof. exact (@lem8132639 A B P z p lt2 t s h1 _107729). Qed.
Lemma lem8132671 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (_107729 : A -> B) (s : P -> A) : (term388 A B P p lt2 t s _107729) = (term321 A B P p lt2 t _107729 s).
Proof. exact (eq_refl (term388 A B P p lt2 t s _107729)). Qed.
Lemma lem8132672 {A B P : Type'} (_107729 : A -> B) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term321 A B P p lt2 t _107729 s.
Proof. exact (EQ_MP (@lem8132671 A B P p lt2 t _107729 s) (@lem8132670 A B P _107729 z p lt2 t s h1)). Qed.
Lemma lem8132673 {A B P : Type'} (_107729 : A -> B) (_107730 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term389 A B P p lt2 t _107729 s _107730.
Proof. exact (@lem8132672 A B P _107729 z p lt2 t s h1 _107730). Qed.
Lemma lem8132674 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (_107729 : A -> B) (s : P -> A) (_107730 : P) : (term389 A B P p lt2 t _107729 s _107730) = (term319 A B P p lt2 t _107729 s _107730).
Proof. exact (eq_refl (term389 A B P p lt2 t _107729 s _107730)). Qed.
Lemma lem8132676 {A B P : Type'} (_107731 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term390 A B P lt2 s a f g _107731.
Proof. exact (@lem8132660 A B P p lt2 s a f g h1 _107731). Qed.
Lemma lem8132677 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107731 : A) : (term390 A B P lt2 s a f g _107731) = (term299 A B P lt2 s a f g _107731).
Proof. exact (eq_refl (term390 A B P lt2 s a f g _107731)). Qed.
Lemma lem8132679 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term391 A B P p z _107726 t _107727 _107728.
Proof. exact (proj2 (@lem8132669 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8132680 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term392 A B P p lt2 z s _107726 t _107727 _107728.
Proof. exact (proj1 (@lem8132669 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8132682 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (h1 : term102 A B P f t g a) : term310 A B P f t g a.
Proof. exact (EQ_MP (@lem8132271 A B P f t g a) (@lem8132125 A B P f t g a h1)). Qed.
Lemma lem8132688 {A B P : Type'} (_107729 : A -> B) (_107730 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term319 A B P p lt2 t _107729 s _107730.
Proof. exact (EQ_MP (@lem8132674 A B P p lt2 t _107729 s _107730) (@lem8132673 A B P _107729 _107730 z p lt2 t s h1)). Qed.
Lemma lem8132698 {A B P : Type'} (_107731 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term299 A B P lt2 s a f g _107731.
Proof. exact (EQ_MP (@lem8132677 A B P lt2 s a f g _107731) (@lem8132676 A B P _107731 p lt2 s a f g h1)). Qed.
Lemma lem8132702 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term392 A B P p lt2 z s _107726 t _107727 _107728) = (term393 A B P p lt2 z s _107726 t _107727 _107728).
Proof. exact (@lem8131077 (term317 A B P p _107726 _107728) (term372 A B P p lt2 z _107726 _107727 s _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8132709 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term394 A B P p lt2 z s _107726 t _107727 _107728) = (term395 A B P p lt2 z s _107726 t _107727 _107728).
Proof. exact (@lem8131077 (term317 A B P p _107727 _107728) (term345 A B P lt2 z _107726 _107727 s _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8132710 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term318 A B P p _107726 _107728) = (term318 A B P p _107726 _107728).
Proof. exact (eq_refl (term318 A B P p _107726 _107728)). Qed.
Lemma lem8132713 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term393 A B P p lt2 z s _107726 t _107727 _107728) = (term396 A B P p lt2 z s _107726 t _107727 _107728).
Proof. exact (MK_COMB (@lem8132710 A B P p _107726 _107728) (@lem8132709 A B P p lt2 z s _107726 t _107727 _107728)). Qed.
Lemma lem8132715 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term392 A B P p lt2 z s _107726 t _107727 _107728) = (term396 A B P p lt2 z s _107726 t _107727 _107728).
Proof. exact (TRANS (@lem8132702 A B P p lt2 z s _107726 t _107727 _107728) (@lem8132713 A B P p lt2 z s _107726 t _107727 _107728)). Qed.
Lemma lem8132716 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term396 A B P p lt2 z s _107726 t _107727 _107728.
Proof. exact (EQ_MP (@lem8132715 A B P p lt2 z s _107726 t _107727 _107728) (@lem8132680 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8132720 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term391 A B P p z _107726 t _107727 _107728) = (term397 A B P p z _107726 t _107727 _107728).
Proof. exact (@lem8131077 (term317 A B P p _107726 _107728) (term373 A B P p z _107726 _107727 _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8132727 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term398 A B P p z _107726 t _107727 _107728) = (term399 A B P p z _107726 t _107727 _107728).
Proof. exact (@lem8131077 (term317 A B P p _107727 _107728) (term338 A B P z _107726 _107727 _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8132728 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term318 A B P p _107726 _107728) = (term318 A B P p _107726 _107728).
Proof. exact (eq_refl (term318 A B P p _107726 _107728)). Qed.
Lemma lem8132731 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term397 A B P p z _107726 t _107727 _107728) = (term400 A B P p z _107726 t _107727 _107728).
Proof. exact (MK_COMB (@lem8132728 A B P p _107726 _107728) (@lem8132727 A B P p z _107726 t _107727 _107728)). Qed.
Lemma lem8132733 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term391 A B P p z _107726 t _107727 _107728) = (term400 A B P p z _107726 t _107727 _107728).
Proof. exact (TRANS (@lem8132720 A B P p z _107726 t _107727 _107728) (@lem8132731 A B P p z _107726 t _107727 _107728)). Qed.
Lemma lem8132734 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term400 A B P p z _107726 t _107727 _107728.
Proof. exact (EQ_MP (@lem8132733 A B P p z _107726 t _107727 _107728) (@lem8132679 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8132848 {A B : Type'} : (@I (A -> B)) = (@I (A -> B)).
Proof. exact (eq_refl (@I (A -> B))). Qed.
Lemma lem8132849 {A B : Type'} (_107760 : A -> B) (_107762 : A -> B) (h1 : _107760 = _107762) : _107760 = _107762.
Proof. exact (h1). Qed.
Lemma lem8132850 {A : Type'} (_107761 : A) (_107763 : A) (h1 : _107761 = _107763) : _107761 = _107763.
Proof. exact (h1). Qed.
Lemma lem8132851 {A B : Type'} (_107760 : A -> B) (_107762 : A -> B) (h1 : _107760 = _107762) : (@I (A -> B) _107760) = (@I (A -> B) _107762).
Proof. exact (MK_COMB (@lem8132848 A B) (@lem8132849 A B _107760 _107762 h1)). Qed.
Lemma lem8132852 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) (h1 : _107761 = _107763) (h2 : _107760 = _107762) : (@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763).
Proof. exact (MK_COMB (@lem8132851 A B _107760 _107762 h2) (@lem8132850 A _107761 _107763 h1)). Qed.
Lemma lem8132853 {A B : Type'} (_107760 : A -> B) (_107762 : A -> B) (_107761 : A) (_107763 : A) (h1 : _107761 = _107763) : term401 A B _107760 _107761 _107762 _107763.
Proof. exact (fun h0 : _107760 = _107762 => @lem8132852 A B _107761 _107763 _107760 _107762 h1 h0). Qed.
Lemma lem8132855 (a : Prop) (b : Prop) : (a -> b) = (term402 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8132856 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : (term401 A B _107760 _107761 _107762 _107763) = (term403 A B _107760 _107761 _107762 _107763).
Proof. exact (@lem8132855 (_107760 = _107762) ((@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763))). Qed.
Lemma lem8132857 {A B : Type'} (_107760 : A -> B) (_107762 : A -> B) (_107761 : A) (_107763 : A) (h1 : _107761 = _107763) : term403 A B _107760 _107761 _107762 _107763.
Proof. exact (EQ_MP (@lem8132856 A B _107760 _107761 _107762 _107763) (@lem8132853 A B _107760 _107762 _107761 _107763 h1)). Qed.
Lemma lem8132858 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : term404 A B _107760 _107761 _107762 _107763.
Proof. exact (fun h0 : _107761 = _107763 => @lem8132857 A B _107760 _107762 _107761 _107763 h0). Qed.
Lemma lem8132860 (a : Prop) (b : Prop) : (a -> b) = (term402 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem8132861 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : (term404 A B _107760 _107761 _107762 _107763) = (term405 A B _107760 _107761 _107762 _107763).
Proof. exact (@lem8132860 (_107761 = _107763) (term403 A B _107760 _107761 _107762 _107763)). Qed.
Lemma lem8132862 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : term405 A B _107760 _107761 _107762 _107763.
Proof. exact (EQ_MP (@lem8132861 A B _107760 _107761 _107762 _107763) (@lem8132858 A B _107760 _107761 _107762 _107763)). Qed.
Lemma lem8132864 {B : Type'} (x : B) (y : B) (z : B) : term406 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem8132886 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p f a.
Proof. exact (proj1 (@lem8132218 A B P p lt2 s a f g h1)). Qed.
Lemma lem8132887 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term407 A B P p f a.
Proof. exact (fun h0 : term317 A B P p f a => @lem8132886 A B P p lt2 s a f g h1). Qed.
Lemma lem8132889 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8132890 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term407 A B P p f a) = (term302 A B P p f a).
Proof. exact (@lem8132889 (term302 A B P p f a)). Qed.
Lemma lem8132891 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p f a.
Proof. exact (EQ_MP (@lem8132890 A B P p f a) (@lem8132887 A B P p lt2 s a f g h1)). Qed.
Lemma lem8132897 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8132898 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : (term319 A B P p lt2 t _107729 s _107730) = (term409 A B P lt2 t s p _107729 _107730).
Proof. exact (@lem8132897 (term316 A B P lt2 t _107729 s _107730) (term317 A B P p _107729 _107730)). Qed.
Lemma lem8132904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8132905 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : (term410 A B P p lt2 t _107729 s _107730) = (term411 A B P lt2 t s p _107729 _107730).
Proof. exact (MK_COMB (@lem8132904) (@lem8132898 A B P lt2 t s p _107729 _107730)). Qed.
Lemma lem8132911 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : (term409 A B P lt2 t s p _107729 _107730) = (term409 A B P lt2 t s p _107729 _107730).
Proof. exact (eq_refl (term409 A B P lt2 t s p _107729 _107730)). Qed.
Lemma lem8132912 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : ((term319 A B P p lt2 t _107729 s _107730) = (term409 A B P lt2 t s p _107729 _107730)) = ((term409 A B P lt2 t s p _107729 _107730) = (term409 A B P lt2 t s p _107729 _107730)).
Proof. exact (MK_COMB (@lem8132905 A B P lt2 t s p _107729 _107730) (@lem8132911 A B P lt2 t s p _107729 _107730)). Qed.
Lemma lem8132914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8132915 (x : Prop) : (x = x) = True.
Proof. exact (@lem8132914 Prop x). Qed.
Lemma lem8132916 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : ((term409 A B P lt2 t s p _107729 _107730) = (term409 A B P lt2 t s p _107729 _107730)) = True.
Proof. exact (@lem8132915 (term409 A B P lt2 t s p _107729 _107730)). Qed.
Lemma lem8132917 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : ((term319 A B P p lt2 t _107729 s _107730) = (term409 A B P lt2 t s p _107729 _107730)) = True.
Proof. exact (TRANS (@lem8132912 A B P lt2 t s p _107729 _107730) (@lem8132916 A B P lt2 t s p _107729 _107730)). Qed.
Lemma lem8132918 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : True = ((term319 A B P p lt2 t _107729 s _107730) = (term409 A B P lt2 t s p _107729 _107730)).
Proof. exact (SYM (@lem8132917 A B P lt2 t s p _107729 _107730)). Qed.
Lemma lem8132919 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : (term319 A B P p lt2 t _107729 s _107730) = (term409 A B P lt2 t s p _107729 _107730).
Proof. exact (EQ_MP (@lem8132918 A B P lt2 t s p _107729 _107730) (@lem0)). Qed.
Lemma lem8132920 {A B P : Type'} (_107729 : A -> B) (_107730 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term409 A B P lt2 t s p _107729 _107730.
Proof. exact (EQ_MP (@lem8132919 A B P lt2 t s p _107729 _107730) (@lem8132688 A B P _107729 _107730 z p lt2 t s h1)). Qed.
Lemma lem8132922 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8132923 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (_107729 : A -> B) (s : P -> A) (_107730 : P) : (term409 A B P lt2 t s p _107729 _107730) = (term413 A B P p lt2 t _107729 s _107730).
Proof. exact (@lem8132922 (term317 A B P p _107729 _107730) (term316 A B P lt2 t _107729 s _107730)). Qed.
Lemma lem8132925 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8132926 {A B P : Type'} (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : (term414 A B P p _107729 _107730) = (term302 A B P p _107729 _107730).
Proof. exact (@lem8132925 (term302 A B P p _107729 _107730)). Qed.
Lemma lem8132927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8132928 {A B P : Type'} (p : type560 A B P) (_107729 : A -> B) (_107730 : P) : (term415 A B P p _107729 _107730) = (term416 A B P p _107729 _107730).
Proof. exact (MK_COMB (@lem8132927) (@lem8132926 A B P p _107729 _107730)). Qed.
Lemma lem8132929 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (_107729 : A -> B) (s : P -> A) (_107730 : P) : (term316 A B P lt2 t _107729 s _107730) = (term316 A B P lt2 t _107729 s _107730).
Proof. exact (eq_refl (term316 A B P lt2 t _107729 s _107730)). Qed.
Lemma lem8132930 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (_107729 : A -> B) (s : P -> A) (_107730 : P) : (term413 A B P p lt2 t _107729 s _107730) = (term417 A B P p lt2 t _107729 s _107730).
Proof. exact (MK_COMB (@lem8132928 A B P p _107729 _107730) (@lem8132929 A B P lt2 t _107729 s _107730)). Qed.
Lemma lem8132931 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (_107729 : A -> B) (s : P -> A) (_107730 : P) : (term409 A B P lt2 t s p _107729 _107730) = (term417 A B P p lt2 t _107729 s _107730).
Proof. exact (TRANS (@lem8132923 A B P p lt2 t _107729 s _107730) (@lem8132930 A B P p lt2 t _107729 s _107730)). Qed.
Lemma lem8132934 {A B P : Type'} (_107729 : A -> B) (_107730 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term417 A B P p lt2 t _107729 s _107730.
Proof. exact (EQ_MP (@lem8132931 A B P p lt2 t _107729 s _107730) (@lem8132920 A B P _107729 _107730 z p lt2 t s h1)). Qed.
Lemma lem8132935 {A B P : Type'} (_107729 : A -> B) (_107730 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term417 A B P p lt2 t _107729 s _107730.
Proof. exact (@lem8132934 A B P _107729 _107730 z p lt2 t s h1). Qed.
Lemma lem8132936 {A B P : Type'} (f : A -> B) (a : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term417 A B P p lt2 t f s a.
Proof. exact (@lem8132935 A B P f a z p lt2 t s h1). Qed.
Lemma lem8132939 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term316 A B P lt2 t f s a.
Proof. exact (@lem8132936 A B P f a z p lt2 t s h1 (@lem8132891 A B P p lt2 s a f g h2)). Qed.
Lemma lem8132940 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term418 A B P lt2 t f s a.
Proof. exact (fun h0 : term419 A B P lt2 t f s a => @lem8132939 A B P z t p lt2 s a f g h1 h2). Qed.
Lemma lem8132942 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8132943 {A B P : Type'} (lt2 : type1402 A) (t : type557 A B P) (f : A -> B) (s : P -> A) (a : P) : (term418 A B P lt2 t f s a) = (term316 A B P lt2 t f s a).
Proof. exact (@lem8132942 (term316 A B P lt2 t f s a)). Qed.
Lemma lem8132944 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term316 A B P lt2 t f s a.
Proof. exact (EQ_MP (@lem8132943 A B P lt2 t f s a) (@lem8132940 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8132950 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8132951 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : (term299 A B P lt2 s a f g _107731) = (term420 A B P f g lt2 _107731 s a).
Proof. exact (@lem8132950 ((@I (A -> B) f _107731) = (@I (A -> B) g _107731)) (term296 A P lt2 _107731 s a)). Qed.
Lemma lem8132959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8132960 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : (term421 A B P lt2 s a f g _107731) = (term422 A B P f g lt2 _107731 s a).
Proof. exact (MK_COMB (@lem8132959) (@lem8132951 A B P f g lt2 _107731 s a)). Qed.
Lemma lem8132968 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : (term420 A B P f g lt2 _107731 s a) = (term420 A B P f g lt2 _107731 s a).
Proof. exact (eq_refl (term420 A B P f g lt2 _107731 s a)). Qed.
Lemma lem8132969 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : ((term299 A B P lt2 s a f g _107731) = (term420 A B P f g lt2 _107731 s a)) = ((term420 A B P f g lt2 _107731 s a) = (term420 A B P f g lt2 _107731 s a)).
Proof. exact (MK_COMB (@lem8132960 A B P f g lt2 _107731 s a) (@lem8132968 A B P f g lt2 _107731 s a)). Qed.
Lemma lem8132971 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8132972 (x : Prop) : (x = x) = True.
Proof. exact (@lem8132971 Prop x). Qed.
Lemma lem8132973 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : ((term420 A B P f g lt2 _107731 s a) = (term420 A B P f g lt2 _107731 s a)) = True.
Proof. exact (@lem8132972 (term420 A B P f g lt2 _107731 s a)). Qed.
Lemma lem8132974 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : ((term299 A B P lt2 s a f g _107731) = (term420 A B P f g lt2 _107731 s a)) = True.
Proof. exact (TRANS (@lem8132969 A B P f g lt2 _107731 s a) (@lem8132973 A B P f g lt2 _107731 s a)). Qed.
Lemma lem8132975 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : True = ((term299 A B P lt2 s a f g _107731) = (term420 A B P f g lt2 _107731 s a)).
Proof. exact (SYM (@lem8132974 A B P f g lt2 _107731 s a)). Qed.
Lemma lem8132976 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : (term299 A B P lt2 s a f g _107731) = (term420 A B P f g lt2 _107731 s a).
Proof. exact (EQ_MP (@lem8132975 A B P f g lt2 _107731 s a) (@lem0)). Qed.
Lemma lem8132977 {A B P : Type'} (_107731 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term420 A B P f g lt2 _107731 s a.
Proof. exact (EQ_MP (@lem8132976 A B P f g lt2 _107731 s a) (@lem8132698 A B P _107731 p lt2 s a f g h1)). Qed.
Lemma lem8132979 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8132980 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107731 : A) : (term420 A B P f g lt2 _107731 s a) = (term423 A B P lt2 s a f g _107731).
Proof. exact (@lem8132979 (term296 A P lt2 _107731 s a) ((@I (A -> B) f _107731) = (@I (A -> B) g _107731))). Qed.
Lemma lem8132982 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8132983 {A P : Type'} (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : (term424 A P lt2 _107731 s a) = (term294 A P lt2 _107731 s a).
Proof. exact (@lem8132982 (term294 A P lt2 _107731 s a)). Qed.
Lemma lem8132984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8132985 {A P : Type'} (lt2 : type1402 A) (_107731 : A) (s : P -> A) (a : P) : (term425 A P lt2 _107731 s a) = (term426 A P lt2 _107731 s a).
Proof. exact (MK_COMB (@lem8132984) (@lem8132983 A P lt2 _107731 s a)). Qed.
Lemma lem8132986 {A B : Type'} (f : A -> B) (g : A -> B) (_107731 : A) : ((@I (A -> B) f _107731) = (@I (A -> B) g _107731)) = ((@I (A -> B) f _107731) = (@I (A -> B) g _107731)).
Proof. exact (eq_refl ((@I (A -> B) f _107731) = (@I (A -> B) g _107731))). Qed.
Lemma lem8132987 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107731 : A) : (term423 A B P lt2 s a f g _107731) = (term427 A B P lt2 s a f g _107731).
Proof. exact (MK_COMB (@lem8132985 A P lt2 _107731 s a) (@lem8132986 A B f g _107731)). Qed.
Lemma lem8132988 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107731 : A) : (term420 A B P f g lt2 _107731 s a) = (term427 A B P lt2 s a f g _107731).
Proof. exact (TRANS (@lem8132980 A B P lt2 s a f g _107731) (@lem8132987 A B P lt2 s a f g _107731)). Qed.
Lemma lem8132991 {A B P : Type'} (_107731 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term427 A B P lt2 s a f g _107731.
Proof. exact (EQ_MP (@lem8132988 A B P lt2 s a f g _107731) (@lem8132977 A B P _107731 p lt2 s a f g h1)). Qed.
Lemma lem8132992 {A B P : Type'} (_107731 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term427 A B P lt2 s a f g _107731.
Proof. exact (@lem8132991 A B P _107731 p lt2 s a f g h1). Qed.
Lemma lem8132993 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term428 A B P lt2 s g t f a.
Proof. exact (@lem8132992 A B P (term306 A B P t f a) p lt2 s a f g h1). Qed.
Lemma lem8132996 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term308 A B P t f a) = (term429 A B P g t f a).
Proof. exact (@lem8132993 A B P t p lt2 s a f g h2 (@lem8132944 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8132997 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term430 A B P g t f a.
Proof. exact (fun h0 : term431 A B P g t f a => @lem8132996 A B P z t p lt2 s a f g h1 h2). Qed.
Lemma lem8132999 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133000 {A B P : Type'} (g : A -> B) (t : type557 A B P) (f : A -> B) (a : P) : (term430 A B P g t f a) = ((term308 A B P t f a) = (term429 A B P g t f a)).
Proof. exact (@lem8132999 ((term308 A B P t f a) = (term429 A B P g t f a))). Qed.
Lemma lem8133001 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term308 A B P t f a) = (term429 A B P g t f a).
Proof. exact (EQ_MP (@lem8133000 A B P g t f a) (@lem8132997 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133003 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem8133004 {B : Type'} (x : B) : x = x.
Proof. exact (@lem8133003 B x). Qed.
Lemma lem8133005 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term308 A B P t f a) = (term308 A B P t f a).
Proof. exact (@lem8133004 B (term308 A B P t f a)). Qed.
Lemma lem8133006 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : term432 A B P t f a.
Proof. exact (fun h0 : term433 A B P t f a => @lem8133005 A B P t f a). Qed.
Lemma lem8133008 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133009 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term432 A B P t f a) = ((term308 A B P t f a) = (term308 A B P t f a)).
Proof. exact (@lem8133008 ((term308 A B P t f a) = (term308 A B P t f a))). Qed.
Lemma lem8133010 {A B P : Type'} (t : type557 A B P) (f : A -> B) (a : P) : (term308 A B P t f a) = (term308 A B P t f a).
Proof. exact (EQ_MP (@lem8133009 A B P t f a) (@lem8133006 A B P t f a)). Qed.
Lemma lem8133028 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8133029 {B : Type'} (y : B) (x : B) (z : B) : (term434 B x y z) = (term435 B y x z).
Proof. exact (@lem8133028 (y = z) (term436 B x z)). Qed.
Lemma lem8133039 {B : Type'} (x : B) (y : B) : (term437 B x y) = (term437 B x y).
Proof. exact (eq_refl (term437 B x y)). Qed.
Lemma lem8133040 {B : Type'} (y : B) (x : B) (z : B) : (term406 B x y z) = (term438 B y x z).
Proof. exact (MK_COMB (@lem8133039 B x y) (@lem8133029 B y x z)). Qed.
Lemma lem8133044 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133045 {B : Type'} (y : B) (x : B) (z : B) : (term438 B y x z) = (term439 B y x z).
Proof. exact (@lem8133044 (y = z) (term436 B x y) (term436 B x z)). Qed.
Lemma lem8133067 {B : Type'} (y : B) (x : B) (z : B) : (term406 B x y z) = (term439 B y x z).
Proof. exact (TRANS (@lem8133040 B y x z) (@lem8133045 B y x z)). Qed.
Lemma lem8133068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8133069 {B : Type'} (y : B) (x : B) (z : B) : (term440 B x y z) = (term441 B y x z).
Proof. exact (MK_COMB (@lem8133068) (@lem8133067 B y x z)). Qed.
Lemma lem8133091 {B : Type'} (y : B) (x : B) (z : B) : (term439 B y x z) = (term439 B y x z).
Proof. exact (eq_refl (term439 B y x z)). Qed.
Lemma lem8133092 {B : Type'} (y : B) (x : B) (z : B) : ((term406 B x y z) = (term439 B y x z)) = ((term439 B y x z) = (term439 B y x z)).
Proof. exact (MK_COMB (@lem8133069 B y x z) (@lem8133091 B y x z)). Qed.
Lemma lem8133094 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8133095 (x : Prop) : (x = x) = True.
Proof. exact (@lem8133094 Prop x). Qed.
Lemma lem8133096 {B : Type'} (y : B) (x : B) (z : B) : ((term439 B y x z) = (term439 B y x z)) = True.
Proof. exact (@lem8133095 (term439 B y x z)). Qed.
Lemma lem8133097 {B : Type'} (y : B) (x : B) (z : B) : ((term406 B x y z) = (term439 B y x z)) = True.
Proof. exact (TRANS (@lem8133092 B y x z) (@lem8133096 B y x z)). Qed.
Lemma lem8133098 {B : Type'} (y : B) (x : B) (z : B) : True = ((term406 B x y z) = (term439 B y x z)).
Proof. exact (SYM (@lem8133097 B y x z)). Qed.
Lemma lem8133099 {B : Type'} (y : B) (x : B) (z : B) : (term406 B x y z) = (term439 B y x z).
Proof. exact (EQ_MP (@lem8133098 B y x z) (@lem0)). Qed.
Lemma lem8133100 {B : Type'} (y : B) (x : B) (z : B) : term439 B y x z.
Proof. exact (EQ_MP (@lem8133099 B y x z) (@lem8132864 B x y z)). Qed.
Lemma lem8133102 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8133103 {B : Type'} (x : B) (y : B) (z : B) : (term439 B y x z) = (term442 B x y z).
Proof. exact (@lem8133102 (term443 B y x z) (y = z)). Qed.
Lemma lem8133105 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8133106 {B : Type'} (y : B) (x : B) (z : B) : (term446 B y x z) = (term447 B y x z).
Proof. exact (@lem8133105 (term436 B x y) (term436 B x z)). Qed.
Lemma lem8133108 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133109 {B : Type'} (x : B) (y : B) : (term448 B x y) = (x = y).
Proof. exact (@lem8133108 (x = y)). Qed.
Lemma lem8133110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8133111 {B : Type'} (x : B) (y : B) : (term449 B x y) = (term450 B x y).
Proof. exact (MK_COMB (@lem8133110) (@lem8133109 B x y)). Qed.
Lemma lem8133113 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133114 {B : Type'} (x : B) (z : B) : (term448 B x z) = (x = z).
Proof. exact (@lem8133113 (x = z)). Qed.
Lemma lem8133115 {B : Type'} (y : B) (x : B) (z : B) : (term447 B y x z) = (term451 B y x z).
Proof. exact (MK_COMB (@lem8133111 B x y) (@lem8133114 B x z)). Qed.
Lemma lem8133116 {B : Type'} (y : B) (x : B) (z : B) : (term446 B y x z) = (term451 B y x z).
Proof. exact (TRANS (@lem8133106 B y x z) (@lem8133115 B y x z)). Qed.
Lemma lem8133117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8133118 {B : Type'} (y : B) (x : B) (z : B) : (term452 B y x z) = (term453 B y x z).
Proof. exact (MK_COMB (@lem8133117) (@lem8133116 B y x z)). Qed.
Lemma lem8133119 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem8133120 {B : Type'} (x : B) (y : B) (z : B) : (term442 B x y z) = (term454 B x y z).
Proof. exact (MK_COMB (@lem8133118 B y x z) (@lem8133119 B y z)). Qed.
Lemma lem8133121 {B : Type'} (x : B) (y : B) (z : B) : (term439 B y x z) = (term454 B x y z).
Proof. exact (TRANS (@lem8133103 B x y z) (@lem8133120 B x y z)). Qed.
Lemma lem8133123 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term455 A B P g t f a.
Proof. exact (conj (@lem8133001 A B P z t p lt2 s a f g h1 h2) (@lem8133010 A B P t f a)). Qed.
Lemma lem8133125 {B : Type'} (x : B) (y : B) (z : B) : term454 B x y z.
Proof. exact (EQ_MP (@lem8133121 B x y z) (@lem8133100 B y x z)). Qed.
Lemma lem8133126 {B : Type'} (x : B) (y : B) (z : B) : term454 B x y z.
Proof. exact (@lem8133125 B x y z). Qed.
Lemma lem8133127 {A B P : Type'} (g : A -> B) (t : type557 A B P) (f : A -> B) (a : P) : term456 A B P g t f a.
Proof. exact (@lem8133126 B (term308 A B P t f a) (term429 A B P g t f a) (term308 A B P t f a)). Qed.
Lemma lem8133130 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term429 A B P g t f a) = (term308 A B P t f a).
Proof. exact (@lem8133127 A B P g t f a (@lem8133123 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133131 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term457 A B P g t f a.
Proof. exact (fun h0 : term458 A B P g t f a => @lem8133130 A B P z t p lt2 s a f g h1 h2). Qed.
Lemma lem8133133 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133134 {A B P : Type'} (g : A -> B) (t : type557 A B P) (f : A -> B) (a : P) : (term457 A B P g t f a) = ((term429 A B P g t f a) = (term308 A B P t f a)).
Proof. exact (@lem8133133 ((term429 A B P g t f a) = (term308 A B P t f a))). Qed.
Lemma lem8133135 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term429 A B P g t f a) = (term308 A B P t f a).
Proof. exact (EQ_MP (@lem8133134 A B P g t f a) (@lem8133131 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133137 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p f a.
Proof. exact (proj1 (@lem8132218 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133138 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term407 A B P p f a.
Proof. exact (fun h0 : term317 A B P p f a => @lem8133137 A B P p lt2 s a f g h1). Qed.
Lemma lem8133140 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133141 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term407 A B P p f a) = (term302 A B P p f a).
Proof. exact (@lem8133140 (term302 A B P p f a)). Qed.
Lemma lem8133142 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p f a.
Proof. exact (EQ_MP (@lem8133141 A B P p f a) (@lem8133138 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133144 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p g a.
Proof. exact (proj1 (@lem8132563 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133145 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term407 A B P p g a.
Proof. exact (fun h0 : term317 A B P p g a => @lem8133144 A B P p lt2 s a f g h1). Qed.
Lemma lem8133147 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133148 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term407 A B P p g a) = (term302 A B P p g a).
Proof. exact (@lem8133147 (term302 A B P p g a)). Qed.
Lemma lem8133149 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p g a.
Proof. exact (EQ_MP (@lem8133148 A B P p g a) (@lem8133145 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133151 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p f a.
Proof. exact (proj1 (@lem8132218 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133152 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term407 A B P p f a.
Proof. exact (fun h0 : term317 A B P p f a => @lem8133151 A B P p lt2 s a f g h1). Qed.
Lemma lem8133154 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133155 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term407 A B P p f a) = (term302 A B P p f a).
Proof. exact (@lem8133154 (term302 A B P p f a)). Qed.
Lemma lem8133156 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p f a.
Proof. exact (EQ_MP (@lem8133155 A B P p f a) (@lem8133152 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133158 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p g a.
Proof. exact (proj1 (@lem8132563 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133159 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term407 A B P p g a.
Proof. exact (fun h0 : term317 A B P p g a => @lem8133158 A B P p lt2 s a f g h1). Qed.
Lemma lem8133161 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133162 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term407 A B P p g a) = (term302 A B P p g a).
Proof. exact (@lem8133161 (term302 A B P p g a)). Qed.
Lemma lem8133163 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term302 A B P p g a.
Proof. exact (EQ_MP (@lem8133162 A B P p g a) (@lem8133159 A B P p lt2 s a f g h1)). Qed.
Lemma lem8133166 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (h1 : term459 A B P f t g a) : term459 A B P f t g a.
Proof. exact (h1). Qed.
Lemma lem8133167 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (h1 : term459 A B P f t g a) : term460 A B P f t g a.
Proof. exact (fun h0 : (term306 A B P t f a) = (term306 A B P t g a) => @lem8133166 A B P f t g a h1). Qed.
Lemma lem8133169 (p : Prop) : (term461 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8133170 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term460 A B P f t g a) = (term459 A B P f t g a).
Proof. exact (@lem8133169 ((term306 A B P t f a) = (term306 A B P t g a))). Qed.
Lemma lem8133171 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (h1 : term459 A B P f t g a) : term459 A B P f t g a.
Proof. exact (EQ_MP (@lem8133170 A B P f t g a) (@lem8133167 A B P f t g a h1)). Qed.
Lemma lem8133187 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133188 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term395 A B P p lt2 z s _107726 t _107727 _107728) = (term462 A B P lt2 z s p _107726 t _107727 _107728).
Proof. exact (@lem8133187 (term345 A B P lt2 z _107726 _107727 s _107728) (term317 A B P p _107727 _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8133202 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8133203 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term463 A B P p _107726 t _107727 _107728) = (term464 A B P _107726 t p _107727 _107728).
Proof. exact (@lem8133202 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133211 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (s : P -> A) (_107728 : P) : (term465 A B P lt2 z _107726 _107727 s _107728) = (term465 A B P lt2 z _107726 _107727 s _107728).
Proof. exact (eq_refl (term465 A B P lt2 z _107726 _107727 s _107728)). Qed.
Lemma lem8133212 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (t : type557 A B P) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term462 A B P lt2 z s p _107726 t _107727 _107728) = (term466 A B P lt2 z s _107726 t p _107727 _107728).
Proof. exact (MK_COMB (@lem8133211 A B P lt2 z _107726 _107727 s _107728) (@lem8133203 A B P _107726 t p _107727 _107728)). Qed.
Lemma lem8133216 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133217 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (s : P -> A) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term466 A B P lt2 z s _107726 t p _107727 _107728) = (term467 A B P t lt2 z _107726 s p _107727 _107728).
Proof. exact (@lem8133216 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term345 A B P lt2 z _107726 _107727 s _107728) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133235 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (s : P -> A) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term462 A B P lt2 z s p _107726 t _107727 _107728) = (term467 A B P t lt2 z _107726 s p _107727 _107728).
Proof. exact (TRANS (@lem8133212 A B P lt2 z s _107726 t p _107727 _107728) (@lem8133217 A B P t lt2 z _107726 s p _107727 _107728)). Qed.
Lemma lem8133236 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (s : P -> A) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term395 A B P p lt2 z s _107726 t _107727 _107728) = (term467 A B P t lt2 z _107726 s p _107727 _107728).
Proof. exact (TRANS (@lem8133188 A B P lt2 z s p _107726 t _107727 _107728) (@lem8133235 A B P t lt2 z _107726 s p _107727 _107728)). Qed.
Lemma lem8133237 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term318 A B P p _107726 _107728) = (term318 A B P p _107726 _107728).
Proof. exact (eq_refl (term318 A B P p _107726 _107728)). Qed.
Lemma lem8133238 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (s : P -> A) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term396 A B P p lt2 z s _107726 t _107727 _107728) = (term468 A B P t lt2 z _107726 s p _107727 _107728).
Proof. exact (MK_COMB (@lem8133237 A B P p _107726 _107728) (@lem8133236 A B P t lt2 z _107726 s p _107727 _107728)). Qed.
Lemma lem8133242 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133243 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (s : P -> A) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term468 A B P t lt2 z _107726 s p _107727 _107728) = (term469 A B P t lt2 z _107726 s p _107727 _107728).
Proof. exact (@lem8133242 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term317 A B P p _107726 _107728) (term470 A B P lt2 z _107726 s p _107727 _107728)). Qed.
Lemma lem8133259 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133260 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term471 A B P lt2 z _107726 s p _107727 _107728) = (term472 A B P lt2 z s _107726 p _107727 _107728).
Proof. exact (@lem8133259 (term345 A B P lt2 z _107726 _107727 s _107728) (term317 A B P p _107726 _107728) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133276 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term473 A B P _107726 t _107727 _107728) = (term473 A B P _107726 t _107727 _107728).
Proof. exact (eq_refl (term473 A B P _107726 t _107727 _107728)). Qed.
Lemma lem8133277 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term469 A B P t lt2 z _107726 s p _107727 _107728) = (term474 A B P t lt2 z s _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133276 A B P _107726 t _107727 _107728) (@lem8133260 A B P lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133288 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term468 A B P t lt2 z _107726 s p _107727 _107728) = (term474 A B P t lt2 z s _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133243 A B P t lt2 z _107726 s p _107727 _107728) (@lem8133277 A B P t lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133289 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term396 A B P p lt2 z s _107726 t _107727 _107728) = (term474 A B P t lt2 z s _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133238 A B P t lt2 z _107726 s p _107727 _107728) (@lem8133288 A B P t lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133290 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8133291 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term475 A B P p lt2 z s _107726 t _107727 _107728) = (term476 A B P t lt2 z s _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133290) (@lem8133289 A B P t lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133315 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8133316 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term463 A B P p _107726 t _107727 _107728) = (term464 A B P _107726 t p _107727 _107728).
Proof. exact (@lem8133315 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133324 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term318 A B P p _107726 _107728) = (term318 A B P p _107726 _107728).
Proof. exact (eq_refl (term318 A B P p _107726 _107728)). Qed.
Lemma lem8133325 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term477 A B P p _107726 t _107727 _107728) = (term478 A B P _107726 t p _107727 _107728).
Proof. exact (MK_COMB (@lem8133324 A B P p _107726 _107728) (@lem8133316 A B P _107726 t p _107727 _107728)). Qed.
Lemma lem8133329 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133330 {A B P : Type'} (t : type557 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term478 A B P _107726 t p _107727 _107728) = (term479 A B P t _107726 p _107727 _107728).
Proof. exact (@lem8133329 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term317 A B P p _107726 _107728) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133348 {A B P : Type'} (t : type557 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term477 A B P p _107726 t _107727 _107728) = (term479 A B P t _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133325 A B P _107726 t p _107727 _107728) (@lem8133330 A B P t _107726 p _107727 _107728)). Qed.
Lemma lem8133349 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (s : P -> A) (_107728 : P) : (term465 A B P lt2 z _107726 _107727 s _107728) = (term465 A B P lt2 z _107726 _107727 s _107728).
Proof. exact (eq_refl (term465 A B P lt2 z _107726 _107727 s _107728)). Qed.
Lemma lem8133350 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (t : type557 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term480 A B P lt2 z s p _107726 t _107727 _107728) = (term481 A B P lt2 z s t _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133349 A B P lt2 z _107726 _107727 s _107728) (@lem8133348 A B P t _107726 p _107727 _107728)). Qed.
Lemma lem8133354 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133355 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term481 A B P lt2 z s t _107726 p _107727 _107728) = (term474 A B P t lt2 z s _107726 p _107727 _107728).
Proof. exact (@lem8133354 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term345 A B P lt2 z _107726 _107727 s _107728) (term482 A B P _107726 p _107727 _107728)). Qed.
Lemma lem8133383 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term480 A B P lt2 z s p _107726 t _107727 _107728) = (term474 A B P t lt2 z s _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133350 A B P lt2 z s t _107726 p _107727 _107728) (@lem8133355 A B P t lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133384 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : ((term396 A B P p lt2 z s _107726 t _107727 _107728) = (term480 A B P lt2 z s p _107726 t _107727 _107728)) = ((term474 A B P t lt2 z s _107726 p _107727 _107728) = (term474 A B P t lt2 z s _107726 p _107727 _107728)).
Proof. exact (MK_COMB (@lem8133291 A B P t lt2 z s _107726 p _107727 _107728) (@lem8133383 A B P t lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133386 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8133387 (x : Prop) : (x = x) = True.
Proof. exact (@lem8133386 Prop x). Qed.
Lemma lem8133388 {A B P : Type'} (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : ((term474 A B P t lt2 z s _107726 p _107727 _107728) = (term474 A B P t lt2 z s _107726 p _107727 _107728)) = True.
Proof. exact (@lem8133387 (term474 A B P t lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133389 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : ((term396 A B P p lt2 z s _107726 t _107727 _107728) = (term480 A B P lt2 z s p _107726 t _107727 _107728)) = True.
Proof. exact (TRANS (@lem8133384 A B P t lt2 z s _107726 p _107727 _107728) (@lem8133388 A B P t lt2 z s _107726 p _107727 _107728)). Qed.
Lemma lem8133390 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : True = ((term396 A B P p lt2 z s _107726 t _107727 _107728) = (term480 A B P lt2 z s p _107726 t _107727 _107728)).
Proof. exact (SYM (@lem8133389 A B P lt2 z s p _107726 t _107727 _107728)). Qed.
Lemma lem8133391 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (s : P -> A) (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term396 A B P p lt2 z s _107726 t _107727 _107728) = (term480 A B P lt2 z s p _107726 t _107727 _107728).
Proof. exact (EQ_MP (@lem8133390 A B P lt2 z s p _107726 t _107727 _107728) (@lem0)). Qed.
Lemma lem8133392 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term480 A B P lt2 z s p _107726 t _107727 _107728.
Proof. exact (EQ_MP (@lem8133391 A B P lt2 z s p _107726 t _107727 _107728) (@lem8132716 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8133394 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8133395 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (s : P -> A) (_107728 : P) : (term480 A B P lt2 z s p _107726 t _107727 _107728) = (term483 A B P p t lt2 z _107726 _107727 s _107728).
Proof. exact (@lem8133394 (term477 A B P p _107726 t _107727 _107728) (term345 A B P lt2 z _107726 _107727 s _107728)). Qed.
Lemma lem8133397 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8133398 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term484 A B P p _107726 t _107727 _107728) = (term485 A B P p _107726 t _107727 _107728).
Proof. exact (@lem8133397 (term317 A B P p _107726 _107728) (term463 A B P p _107726 t _107727 _107728)). Qed.
Lemma lem8133400 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133401 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term414 A B P p _107726 _107728) = (term302 A B P p _107726 _107728).
Proof. exact (@lem8133400 (term302 A B P p _107726 _107728)). Qed.
Lemma lem8133402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8133403 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term486 A B P p _107726 _107728) = (term303 A B P p _107726 _107728).
Proof. exact (MK_COMB (@lem8133402) (@lem8133401 A B P p _107726 _107728)). Qed.
Lemma lem8133405 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8133406 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term487 A B P p _107726 t _107727 _107728) = (term488 A B P p _107726 t _107727 _107728).
Proof. exact (@lem8133405 (term317 A B P p _107727 _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8133408 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133409 {A B P : Type'} (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term414 A B P p _107727 _107728) = (term302 A B P p _107727 _107728).
Proof. exact (@lem8133408 (term302 A B P p _107727 _107728)). Qed.
Lemma lem8133410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8133411 {A B P : Type'} (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term486 A B P p _107727 _107728) = (term303 A B P p _107727 _107728).
Proof. exact (MK_COMB (@lem8133410) (@lem8133409 A B P p _107727 _107728)). Qed.
Lemma lem8133412 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term459 A B P _107726 t _107727 _107728) = (term459 A B P _107726 t _107727 _107728).
Proof. exact (eq_refl (term459 A B P _107726 t _107727 _107728)). Qed.
Lemma lem8133413 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term488 A B P p _107726 t _107727 _107728) = (term489 A B P p _107726 t _107727 _107728).
Proof. exact (MK_COMB (@lem8133411 A B P p _107727 _107728) (@lem8133412 A B P _107726 t _107727 _107728)). Qed.
Lemma lem8133414 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term487 A B P p _107726 t _107727 _107728) = (term489 A B P p _107726 t _107727 _107728).
Proof. exact (TRANS (@lem8133406 A B P p _107726 t _107727 _107728) (@lem8133413 A B P p _107726 t _107727 _107728)). Qed.
Lemma lem8133415 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term485 A B P p _107726 t _107727 _107728) = (term490 A B P p _107726 t _107727 _107728).
Proof. exact (MK_COMB (@lem8133403 A B P p _107726 _107728) (@lem8133414 A B P p _107726 t _107727 _107728)). Qed.
Lemma lem8133416 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term484 A B P p _107726 t _107727 _107728) = (term490 A B P p _107726 t _107727 _107728).
Proof. exact (TRANS (@lem8133398 A B P p _107726 t _107727 _107728) (@lem8133415 A B P p _107726 t _107727 _107728)). Qed.
Lemma lem8133417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8133418 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term491 A B P p _107726 t _107727 _107728) = (term492 A B P p _107726 t _107727 _107728).
Proof. exact (MK_COMB (@lem8133417) (@lem8133416 A B P p _107726 t _107727 _107728)). Qed.
Lemma lem8133419 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (s : P -> A) (_107728 : P) : (term345 A B P lt2 z _107726 _107727 s _107728) = (term345 A B P lt2 z _107726 _107727 s _107728).
Proof. exact (eq_refl (term345 A B P lt2 z _107726 _107727 s _107728)). Qed.
Lemma lem8133420 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (s : P -> A) (_107728 : P) : (term483 A B P p t lt2 z _107726 _107727 s _107728) = (term493 A B P p t lt2 z _107726 _107727 s _107728).
Proof. exact (MK_COMB (@lem8133418 A B P p _107726 t _107727 _107728) (@lem8133419 A B P lt2 z _107726 _107727 s _107728)). Qed.
Lemma lem8133421 {A B P : Type'} (p : type560 A B P) (t : type557 A B P) (lt2 : type1402 A) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (s : P -> A) (_107728 : P) : (term480 A B P lt2 z s p _107726 t _107727 _107728) = (term493 A B P p t lt2 z _107726 _107727 s _107728).
Proof. exact (TRANS (@lem8133395 A B P p t lt2 z _107726 _107727 s _107728) (@lem8133420 A B P p t lt2 z _107726 _107727 s _107728)). Qed.
Lemma lem8133423 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term90 A B P p lt2 s a f g) : term489 A B P p f t g a.
Proof. exact (conj (@lem8133163 A B P p lt2 s a f g h2) (@lem8133171 A B P f t g a h1)). Qed.
Lemma lem8133424 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term90 A B P p lt2 s a f g) : term490 A B P p f t g a.
Proof. exact (conj (@lem8133156 A B P p lt2 s a f g h2) (@lem8133423 A B P t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133426 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term493 A B P p t lt2 z _107726 _107727 s _107728.
Proof. exact (EQ_MP (@lem8133421 A B P p t lt2 z _107726 _107727 s _107728) (@lem8133392 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8133427 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term493 A B P p t lt2 z _107726 _107727 s _107728.
Proof. exact (@lem8133426 A B P _107726 _107727 _107728 z p lt2 t s h1). Qed.
Lemma lem8133428 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term493 A B P p t lt2 z f g s a.
Proof. exact (@lem8133427 A B P f g a z p lt2 t s h1). Qed.
Lemma lem8133431 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : term345 A B P lt2 z f g s a.
Proof. exact (@lem8133428 A B P f g a z p lt2 t s h2 (@lem8133424 A B P t p lt2 s a f g h1 h3)). Qed.
Lemma lem8133432 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : term494 A B P lt2 z f g s a.
Proof. exact (fun h0 : term495 A B P lt2 z f g s a => @lem8133431 A B P z t p lt2 s a f g h1 h2 h3). Qed.
Lemma lem8133434 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133435 {A B P : Type'} (lt2 : type1402 A) (z : type518 A B P) (f : A -> B) (g : A -> B) (s : P -> A) (a : P) : (term494 A B P lt2 z f g s a) = (term345 A B P lt2 z f g s a).
Proof. exact (@lem8133434 (term345 A B P lt2 z f g s a)). Qed.
Lemma lem8133436 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : term345 A B P lt2 z f g s a.
Proof. exact (EQ_MP (@lem8133435 A B P lt2 z f g s a) (@lem8133432 A B P z t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8133438 {A B P : Type'} (_107731 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term427 A B P lt2 s a f g _107731.
Proof. exact (EQ_MP (@lem8132988 A B P lt2 s a f g _107731) (@lem8132977 A B P _107731 p lt2 s a f g h1)). Qed.
Lemma lem8133439 {A B P : Type'} (_107731 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term427 A B P lt2 s a f g _107731.
Proof. exact (@lem8133438 A B P _107731 p lt2 s a f g h1). Qed.
Lemma lem8133440 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term90 A B P p lt2 s a f g) : term496 A B P lt2 s z f g a.
Proof. exact (@lem8133439 A B P (term328 A B P z f g a) p lt2 s a f g h1). Qed.
Lemma lem8133443 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : (term331 A B P z f g a) = (term334 A B P z f g a).
Proof. exact (@lem8133440 A B P z p lt2 s a f g h3 (@lem8133436 A B P z t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8133444 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : term497 A B P z f g a.
Proof. exact (fun h0 : term338 A B P z f g a => @lem8133443 A B P z t p lt2 s a f g h1 h2 h3). Qed.
Lemma lem8133446 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133447 {A B P : Type'} (z : type518 A B P) (f : A -> B) (g : A -> B) (a : P) : (term497 A B P z f g a) = ((term331 A B P z f g a) = (term334 A B P z f g a)).
Proof. exact (@lem8133446 ((term331 A B P z f g a) = (term334 A B P z f g a))). Qed.
Lemma lem8133448 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : (term331 A B P z f g a) = (term334 A B P z f g a).
Proof. exact (EQ_MP (@lem8133447 A B P z f g a) (@lem8133444 A B P z t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8133464 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133465 {A B P : Type'} (z : type518 A B P) (p : type560 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term399 A B P p z _107726 t _107727 _107728) = (term498 A B P z p _107726 t _107727 _107728).
Proof. exact (@lem8133464 (term338 A B P z _107726 _107727 _107728) (term317 A B P p _107727 _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8133481 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8133482 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term463 A B P p _107726 t _107727 _107728) = (term464 A B P _107726 t p _107727 _107728).
Proof. exact (@lem8133481 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133490 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term499 A B P z _107726 _107727 _107728) = (term499 A B P z _107726 _107727 _107728).
Proof. exact (eq_refl (term499 A B P z _107726 _107727 _107728)). Qed.
Lemma lem8133491 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term498 A B P z p _107726 t _107727 _107728) = (term500 A B P z _107726 t p _107727 _107728).
Proof. exact (MK_COMB (@lem8133490 A B P z _107726 _107727 _107728) (@lem8133482 A B P _107726 t p _107727 _107728)). Qed.
Lemma lem8133495 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133496 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term500 A B P z _107726 t p _107727 _107728) = (term501 A B P t z _107726 p _107727 _107728).
Proof. exact (@lem8133495 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term338 A B P z _107726 _107727 _107728) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133516 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term498 A B P z p _107726 t _107727 _107728) = (term501 A B P t z _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133491 A B P z _107726 t p _107727 _107728) (@lem8133496 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133517 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term399 A B P p z _107726 t _107727 _107728) = (term501 A B P t z _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133465 A B P z p _107726 t _107727 _107728) (@lem8133516 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133518 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term318 A B P p _107726 _107728) = (term318 A B P p _107726 _107728).
Proof. exact (eq_refl (term318 A B P p _107726 _107728)). Qed.
Lemma lem8133519 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term400 A B P p z _107726 t _107727 _107728) = (term502 A B P t z _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133518 A B P p _107726 _107728) (@lem8133517 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133523 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133524 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term502 A B P t z _107726 p _107727 _107728) = (term503 A B P t z _107726 p _107727 _107728).
Proof. exact (@lem8133523 ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) (term317 A B P p _107726 _107728) (term504 A B P z _107726 p _107727 _107728)). Qed.
Lemma lem8133540 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133541 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term505 A B P z _107726 p _107727 _107728) = (term506 A B P z _107726 p _107727 _107728).
Proof. exact (@lem8133540 (term338 A B P z _107726 _107727 _107728) (term317 A B P p _107726 _107728) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133559 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term473 A B P _107726 t _107727 _107728) = (term473 A B P _107726 t _107727 _107728).
Proof. exact (eq_refl (term473 A B P _107726 t _107727 _107728)). Qed.
Lemma lem8133560 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term503 A B P t z _107726 p _107727 _107728) = (term507 A B P t z _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133559 A B P _107726 t _107727 _107728) (@lem8133541 A B P z _107726 p _107727 _107728)). Qed.
Lemma lem8133571 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term502 A B P t z _107726 p _107727 _107728) = (term507 A B P t z _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133524 A B P t z _107726 p _107727 _107728) (@lem8133560 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133572 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term400 A B P p z _107726 t _107727 _107728) = (term507 A B P t z _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133519 A B P t z _107726 p _107727 _107728) (@lem8133571 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8133574 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term508 A B P p z _107726 t _107727 _107728) = (term509 A B P t z _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133573) (@lem8133572 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133600 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8133601 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term373 A B P p z _107726 _107727 _107728) = (term504 A B P z _107726 p _107727 _107728).
Proof. exact (@lem8133600 (term338 A B P z _107726 _107727 _107728) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133609 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term318 A B P p _107726 _107728) = (term318 A B P p _107726 _107728).
Proof. exact (eq_refl (term318 A B P p _107726 _107728)). Qed.
Lemma lem8133610 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term378 A B P p z _107726 _107727 _107728) = (term505 A B P z _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133609 A B P p _107726 _107728) (@lem8133601 A B P z _107726 p _107727 _107728)). Qed.
Lemma lem8133614 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133615 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term505 A B P z _107726 p _107727 _107728) = (term506 A B P z _107726 p _107727 _107728).
Proof. exact (@lem8133614 (term338 A B P z _107726 _107727 _107728) (term317 A B P p _107726 _107728) (term317 A B P p _107727 _107728)). Qed.
Lemma lem8133633 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term378 A B P p z _107726 _107727 _107728) = (term506 A B P z _107726 p _107727 _107728).
Proof. exact (TRANS (@lem8133610 A B P z _107726 p _107727 _107728) (@lem8133615 A B P z _107726 p _107727 _107728)). Qed.
Lemma lem8133634 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term473 A B P _107726 t _107727 _107728) = (term473 A B P _107726 t _107727 _107728).
Proof. exact (eq_refl (term473 A B P _107726 t _107727 _107728)). Qed.
Lemma lem8133635 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term510 A B P t p z _107726 _107727 _107728) = (term507 A B P t z _107726 p _107727 _107728).
Proof. exact (MK_COMB (@lem8133634 A B P _107726 t _107727 _107728) (@lem8133633 A B P z _107726 p _107727 _107728)). Qed.
Lemma lem8133646 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : ((term400 A B P p z _107726 t _107727 _107728) = (term510 A B P t p z _107726 _107727 _107728)) = ((term507 A B P t z _107726 p _107727 _107728) = (term507 A B P t z _107726 p _107727 _107728)).
Proof. exact (MK_COMB (@lem8133574 A B P t z _107726 p _107727 _107728) (@lem8133635 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133648 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8133649 (x : Prop) : (x = x) = True.
Proof. exact (@lem8133648 Prop x). Qed.
Lemma lem8133650 {A B P : Type'} (t : type557 A B P) (z : type518 A B P) (_107726 : A -> B) (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : ((term507 A B P t z _107726 p _107727 _107728) = (term507 A B P t z _107726 p _107727 _107728)) = True.
Proof. exact (@lem8133649 (term507 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133651 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : ((term400 A B P p z _107726 t _107727 _107728) = (term510 A B P t p z _107726 _107727 _107728)) = True.
Proof. exact (TRANS (@lem8133646 A B P t z _107726 p _107727 _107728) (@lem8133650 A B P t z _107726 p _107727 _107728)). Qed.
Lemma lem8133652 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : True = ((term400 A B P p z _107726 t _107727 _107728) = (term510 A B P t p z _107726 _107727 _107728)).
Proof. exact (SYM (@lem8133651 A B P t p z _107726 _107727 _107728)). Qed.
Lemma lem8133653 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term400 A B P p z _107726 t _107727 _107728) = (term510 A B P t p z _107726 _107727 _107728).
Proof. exact (EQ_MP (@lem8133652 A B P t p z _107726 _107727 _107728) (@lem0)). Qed.
Lemma lem8133654 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term510 A B P t p z _107726 _107727 _107728.
Proof. exact (EQ_MP (@lem8133653 A B P t p z _107726 _107727 _107728) (@lem8132734 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8133656 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8133657 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term510 A B P t p z _107726 _107727 _107728) = (term511 A B P p z _107726 t _107727 _107728).
Proof. exact (@lem8133656 (term378 A B P p z _107726 _107727 _107728) ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8133659 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8133660 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term512 A B P p z _107726 _107727 _107728) = (term513 A B P p z _107726 _107727 _107728).
Proof. exact (@lem8133659 (term317 A B P p _107726 _107728) (term373 A B P p z _107726 _107727 _107728)). Qed.
Lemma lem8133662 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133663 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term414 A B P p _107726 _107728) = (term302 A B P p _107726 _107728).
Proof. exact (@lem8133662 (term302 A B P p _107726 _107728)). Qed.
Lemma lem8133664 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8133665 {A B P : Type'} (p : type560 A B P) (_107726 : A -> B) (_107728 : P) : (term486 A B P p _107726 _107728) = (term303 A B P p _107726 _107728).
Proof. exact (MK_COMB (@lem8133664) (@lem8133663 A B P p _107726 _107728)). Qed.
Lemma lem8133667 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8133668 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term514 A B P p z _107726 _107727 _107728) = (term515 A B P p z _107726 _107727 _107728).
Proof. exact (@lem8133667 (term317 A B P p _107727 _107728) (term338 A B P z _107726 _107727 _107728)). Qed.
Lemma lem8133670 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133671 {A B P : Type'} (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term414 A B P p _107727 _107728) = (term302 A B P p _107727 _107728).
Proof. exact (@lem8133670 (term302 A B P p _107727 _107728)). Qed.
Lemma lem8133672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8133673 {A B P : Type'} (p : type560 A B P) (_107727 : A -> B) (_107728 : P) : (term486 A B P p _107727 _107728) = (term303 A B P p _107727 _107728).
Proof. exact (MK_COMB (@lem8133672) (@lem8133671 A B P p _107727 _107728)). Qed.
Lemma lem8133675 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133676 {A B P : Type'} (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term516 A B P z _107726 _107727 _107728) = ((term331 A B P z _107726 _107727 _107728) = (term334 A B P z _107726 _107727 _107728)).
Proof. exact (@lem8133675 ((term331 A B P z _107726 _107727 _107728) = (term334 A B P z _107726 _107727 _107728))). Qed.
Lemma lem8133677 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term515 A B P p z _107726 _107727 _107728) = (term517 A B P p z _107726 _107727 _107728).
Proof. exact (MK_COMB (@lem8133673 A B P p _107727 _107728) (@lem8133676 A B P z _107726 _107727 _107728)). Qed.
Lemma lem8133678 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term514 A B P p z _107726 _107727 _107728) = (term517 A B P p z _107726 _107727 _107728).
Proof. exact (TRANS (@lem8133668 A B P p z _107726 _107727 _107728) (@lem8133677 A B P p z _107726 _107727 _107728)). Qed.
Lemma lem8133679 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term513 A B P p z _107726 _107727 _107728) = (term518 A B P p z _107726 _107727 _107728).
Proof. exact (MK_COMB (@lem8133665 A B P p _107726 _107728) (@lem8133678 A B P p z _107726 _107727 _107728)). Qed.
Lemma lem8133680 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term512 A B P p z _107726 _107727 _107728) = (term518 A B P p z _107726 _107727 _107728).
Proof. exact (TRANS (@lem8133660 A B P p z _107726 _107727 _107728) (@lem8133679 A B P p z _107726 _107727 _107728)). Qed.
Lemma lem8133681 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8133682 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) : (term519 A B P p z _107726 _107727 _107728) = (term520 A B P p z _107726 _107727 _107728).
Proof. exact (MK_COMB (@lem8133681) (@lem8133680 A B P p z _107726 _107727 _107728)). Qed.
Lemma lem8133683 {A B P : Type'} (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)) = ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728)).
Proof. exact (eq_refl ((term306 A B P t _107726 _107728) = (term306 A B P t _107727 _107728))). Qed.
Lemma lem8133684 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term511 A B P p z _107726 t _107727 _107728) = (term521 A B P p z _107726 t _107727 _107728).
Proof. exact (MK_COMB (@lem8133682 A B P p z _107726 _107727 _107728) (@lem8133683 A B P _107726 t _107727 _107728)). Qed.
Lemma lem8133685 {A B P : Type'} (p : type560 A B P) (z : type518 A B P) (_107726 : A -> B) (t : type557 A B P) (_107727 : A -> B) (_107728 : P) : (term510 A B P t p z _107726 _107727 _107728) = (term521 A B P p z _107726 t _107727 _107728).
Proof. exact (TRANS (@lem8133657 A B P p z _107726 t _107727 _107728) (@lem8133684 A B P p z _107726 t _107727 _107728)). Qed.
Lemma lem8133687 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : term517 A B P p z f g a.
Proof. exact (conj (@lem8133149 A B P p lt2 s a f g h3) (@lem8133448 A B P z t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8133688 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : term518 A B P p z f g a.
Proof. exact (conj (@lem8133142 A B P p lt2 s a f g h3) (@lem8133687 A B P z t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8133690 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term521 A B P p z _107726 t _107727 _107728.
Proof. exact (EQ_MP (@lem8133685 A B P p z _107726 t _107727 _107728) (@lem8133654 A B P _107726 _107727 _107728 z p lt2 t s h1)). Qed.
Lemma lem8133691 {A B P : Type'} (_107726 : A -> B) (_107727 : A -> B) (_107728 : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term521 A B P p z _107726 t _107727 _107728.
Proof. exact (@lem8133690 A B P _107726 _107727 _107728 z p lt2 t s h1). Qed.
Lemma lem8133692 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (z : type518 A B P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term281 A B P z p lt2 t s) : term521 A B P p z f t g a.
Proof. exact (@lem8133691 A B P f g a z p lt2 t s h1). Qed.
Lemma lem8133695 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term459 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : (term306 A B P t f a) = (term306 A B P t g a).
Proof. exact (@lem8133692 A B P f g a z p lt2 t s h2 (@lem8133688 A B P z t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8133696 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term522 A B P f t g a.
Proof. exact (fun h0 : term459 A B P f t g a => @lem8133695 A B P z t p lt2 s a f g h0 h1 h2). Qed.
Lemma lem8133698 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133699 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term522 A B P f t g a) = ((term306 A B P t f a) = (term306 A B P t g a)).
Proof. exact (@lem8133698 ((term306 A B P t f a) = (term306 A B P t g a))). Qed.
Lemma lem8133700 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term306 A B P t f a) = (term306 A B P t g a).
Proof. exact (EQ_MP (@lem8133699 A B P f t g a) (@lem8133696 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133702 {A B : Type'} (x : A -> B) : x = x.
Proof. exact (@lem21386 (A -> B) x). Qed.
Lemma lem8133703 {A B : Type'} (x : A -> B) : x = x.
Proof. exact (@lem8133702 A B x). Qed.
Lemma lem8133704 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (@lem8133703 A B g). Qed.
Lemma lem8133705 {A B : Type'} (g : A -> B) : term523 A B g.
Proof. exact (fun h0 : term524 A B g => @lem8133704 A B g). Qed.
Lemma lem8133707 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133708 {A B : Type'} (g : A -> B) : (term523 A B g) = (g = g).
Proof. exact (@lem8133707 (g = g)). Qed.
Lemma lem8133709 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (EQ_MP (@lem8133708 A B g) (@lem8133705 A B g)). Qed.
Lemma lem8133727 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8133728 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term403 A B _107760 _107761 _107762 _107763) = (term525 A B _107761 _107763 _107760 _107762).
Proof. exact (@lem8133727 ((@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763)) (term526 A B _107760 _107762)). Qed.
Lemma lem8133738 {A : Type'} (_107761 : A) (_107763 : A) : (term437 A _107761 _107763) = (term437 A _107761 _107763).
Proof. exact (eq_refl (term437 A _107761 _107763)). Qed.
Lemma lem8133739 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term405 A B _107760 _107761 _107762 _107763) = (term527 A B _107761 _107763 _107760 _107762).
Proof. exact (MK_COMB (@lem8133738 A _107761 _107763) (@lem8133728 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133743 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8133744 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term527 A B _107761 _107763 _107760 _107762) = (term528 A B _107761 _107763 _107760 _107762).
Proof. exact (@lem8133743 ((@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763)) (term436 A _107761 _107763) (term526 A B _107760 _107762)). Qed.
Lemma lem8133766 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term405 A B _107760 _107761 _107762 _107763) = (term528 A B _107761 _107763 _107760 _107762).
Proof. exact (TRANS (@lem8133739 A B _107761 _107763 _107760 _107762) (@lem8133744 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8133768 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term529 A B _107760 _107761 _107762 _107763) = (term530 A B _107761 _107763 _107760 _107762).
Proof. exact (MK_COMB (@lem8133767) (@lem8133766 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133790 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term528 A B _107761 _107763 _107760 _107762) = (term528 A B _107761 _107763 _107760 _107762).
Proof. exact (eq_refl (term528 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133791 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : ((term405 A B _107760 _107761 _107762 _107763) = (term528 A B _107761 _107763 _107760 _107762)) = ((term528 A B _107761 _107763 _107760 _107762) = (term528 A B _107761 _107763 _107760 _107762)).
Proof. exact (MK_COMB (@lem8133768 A B _107761 _107763 _107760 _107762) (@lem8133790 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133793 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8133794 (x : Prop) : (x = x) = True.
Proof. exact (@lem8133793 Prop x). Qed.
Lemma lem8133795 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : ((term528 A B _107761 _107763 _107760 _107762) = (term528 A B _107761 _107763 _107760 _107762)) = True.
Proof. exact (@lem8133794 (term528 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133796 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : ((term405 A B _107760 _107761 _107762 _107763) = (term528 A B _107761 _107763 _107760 _107762)) = True.
Proof. exact (TRANS (@lem8133791 A B _107761 _107763 _107760 _107762) (@lem8133795 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133797 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : True = ((term405 A B _107760 _107761 _107762 _107763) = (term528 A B _107761 _107763 _107760 _107762)).
Proof. exact (SYM (@lem8133796 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133798 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term405 A B _107760 _107761 _107762 _107763) = (term528 A B _107761 _107763 _107760 _107762).
Proof. exact (EQ_MP (@lem8133797 A B _107761 _107763 _107760 _107762) (@lem0)). Qed.
Lemma lem8133799 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : term528 A B _107761 _107763 _107760 _107762.
Proof. exact (EQ_MP (@lem8133798 A B _107761 _107763 _107760 _107762) (@lem8132862 A B _107760 _107761 _107762 _107763)). Qed.
Lemma lem8133801 (b : Prop) (a : Prop) : (a \/ b) = (term412 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8133802 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : (term528 A B _107761 _107763 _107760 _107762) = (term531 A B _107760 _107761 _107762 _107763).
Proof. exact (@lem8133801 (term532 A B _107761 _107763 _107760 _107762) ((@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763))). Qed.
Lemma lem8133804 (a : Prop) (b : Prop) : (term444 a b) = (term445 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8133805 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term533 A B _107761 _107763 _107760 _107762) = (term534 A B _107761 _107763 _107760 _107762).
Proof. exact (@lem8133804 (term436 A _107761 _107763) (term526 A B _107760 _107762)). Qed.
Lemma lem8133807 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133808 {A : Type'} (_107761 : A) (_107763 : A) : (term448 A _107761 _107763) = (_107761 = _107763).
Proof. exact (@lem8133807 (_107761 = _107763)). Qed.
Lemma lem8133809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8133810 {A : Type'} (_107761 : A) (_107763 : A) : (term449 A _107761 _107763) = (term450 A _107761 _107763).
Proof. exact (MK_COMB (@lem8133809) (@lem8133808 A _107761 _107763)). Qed.
Lemma lem8133812 (a : Prop) : (term84 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8133813 {A B : Type'} (_107760 : A -> B) (_107762 : A -> B) : (term535 A B _107760 _107762) = (_107760 = _107762).
Proof. exact (@lem8133812 (_107760 = _107762)). Qed.
Lemma lem8133814 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term534 A B _107761 _107763 _107760 _107762) = (term536 A B _107761 _107763 _107760 _107762).
Proof. exact (MK_COMB (@lem8133810 A _107761 _107763) (@lem8133813 A B _107760 _107762)). Qed.
Lemma lem8133815 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term533 A B _107761 _107763 _107760 _107762) = (term536 A B _107761 _107763 _107760 _107762).
Proof. exact (TRANS (@lem8133805 A B _107761 _107763 _107760 _107762) (@lem8133814 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8133817 {A B : Type'} (_107761 : A) (_107763 : A) (_107760 : A -> B) (_107762 : A -> B) : (term537 A B _107761 _107763 _107760 _107762) = (term538 A B _107761 _107763 _107760 _107762).
Proof. exact (MK_COMB (@lem8133816) (@lem8133815 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133818 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : ((@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763)) = ((@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763)).
Proof. exact (eq_refl ((@I (A -> B) _107760 _107761) = (@I (A -> B) _107762 _107763))). Qed.
Lemma lem8133819 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : (term531 A B _107760 _107761 _107762 _107763) = (term539 A B _107760 _107761 _107762 _107763).
Proof. exact (MK_COMB (@lem8133817 A B _107761 _107763 _107760 _107762) (@lem8133818 A B _107760 _107761 _107762 _107763)). Qed.
Lemma lem8133820 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : (term528 A B _107761 _107763 _107760 _107762) = (term539 A B _107760 _107761 _107762 _107763).
Proof. exact (TRANS (@lem8133802 A B _107760 _107761 _107762 _107763) (@lem8133819 A B _107760 _107761 _107762 _107763)). Qed.
Lemma lem8133822 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term540 A B P f t a g.
Proof. exact (conj (@lem8133700 A B P z t p lt2 s a f g h1 h2) (@lem8133709 A B g)). Qed.
Lemma lem8133824 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : term539 A B _107760 _107761 _107762 _107763.
Proof. exact (EQ_MP (@lem8133820 A B _107760 _107761 _107762 _107763) (@lem8133799 A B _107761 _107763 _107760 _107762)). Qed.
Lemma lem8133825 {A B : Type'} (_107760 : A -> B) (_107761 : A) (_107762 : A -> B) (_107763 : A) : term539 A B _107760 _107761 _107762 _107763.
Proof. exact (@lem8133824 A B _107760 _107761 _107762 _107763). Qed.
Lemma lem8133826 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : term541 A B P f t g a.
Proof. exact (@lem8133825 A B g (term306 A B P t f a) g (term306 A B P t g a)). Qed.
Lemma lem8133829 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term429 A B P g t f a) = (term308 A B P t g a).
Proof. exact (@lem8133826 A B P f t g a (@lem8133822 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133830 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term542 A B P f t g a.
Proof. exact (fun h0 : term543 A B P f t g a => @lem8133829 A B P z t p lt2 s a f g h1 h2). Qed.
Lemma lem8133832 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133833 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term542 A B P f t g a) = ((term429 A B P g t f a) = (term308 A B P t g a)).
Proof. exact (@lem8133832 ((term429 A B P g t f a) = (term308 A B P t g a))). Qed.
Lemma lem8133834 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term429 A B P g t f a) = (term308 A B P t g a).
Proof. exact (EQ_MP (@lem8133833 A B P f t g a) (@lem8133830 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133835 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term544 A B P f t g a.
Proof. exact (conj (@lem8133135 A B P z t p lt2 s a f g h1 h2) (@lem8133834 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133837 {B : Type'} (x : B) (y : B) (z : B) : term454 B x y z.
Proof. exact (EQ_MP (@lem8133121 B x y z) (@lem8133100 B y x z)). Qed.
Lemma lem8133838 {B : Type'} (x : B) (y : B) (z : B) : term454 B x y z.
Proof. exact (@lem8133837 B x y z). Qed.
Lemma lem8133839 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : term545 A B P f t g a.
Proof. exact (@lem8133838 B (term429 A B P g t f a) (term308 A B P t f a) (term308 A B P t g a)). Qed.
Lemma lem8133842 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term308 A B P t f a) = (term308 A B P t g a).
Proof. exact (@lem8133839 A B P f t g a (@lem8133835 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133843 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term546 A B P f t g a.
Proof. exact (fun h0 : term310 A B P f t g a => @lem8133842 A B P z t p lt2 s a f g h1 h2). Qed.
Lemma lem8133845 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133846 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term546 A B P f t g a) = ((term308 A B P t f a) = (term308 A B P t g a)).
Proof. exact (@lem8133845 ((term308 A B P t f a) = (term308 A B P t g a))). Qed.
Lemma lem8133847 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term281 A B P z p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term308 A B P t f a) = (term308 A B P t g a).
Proof. exact (EQ_MP (@lem8133846 A B P f t g a) (@lem8133843 A B P z t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133850 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8133852 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) : (term310 A B P f t g a) = (term547 A B P f t g a).
Proof. exact (@lem8133850 ((term308 A B P t f a) = (term308 A B P t g a))). Qed.
Lemma lem8133855 {A B P : Type'} (f : A -> B) (t : type557 A B P) (g : A -> B) (a : P) (h1 : term102 A B P f t g a) : term547 A B P f t g a.
Proof. exact (EQ_MP (@lem8133852 A B P f t g a) (@lem8132682 A B P f t g a h1)). Qed.
Lemma lem8133858 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : False.
Proof. exact (@lem8133855 A B P f t g a h1 (@lem8133847 A B P z t p lt2 s a f g h2 h3)). Qed.
Lemma lem8133859 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : term548.
Proof. exact (fun h0 : ~ False => @lem8133858 A B P z t p lt2 s a f g h1 h2 h3). Qed.
Lemma lem8133861 (p : Prop) : (term408 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8133862 : term548 = False.
Proof. exact (@lem8133861 False). Qed.
Lemma lem8133863 {A B P : Type'} (z : type518 A B P) (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term281 A B P z p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8133862) (@lem8133859 A B P z t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8133864 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term20 A B P p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : False.
Proof. exact (ex_elim (@lem8132048 A B P p lt2 t s h2) (fun z : type518 A B P => fun h0 : term283 A B P p lt2 t s z => @lem8133863 A B P z t p lt2 s a f g h1 h0 h3)). Qed.
Lemma lem8133865 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term20 A B P p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : (term102 A B P f t g a) = False.
Proof. exact (prop_ext (fun h4 : term102 A B P f t g a => @lem8133864 A B P t p lt2 s a f g h1 h2 h3) (fun h4 : False => @lem8132125 A B P f t g a h1)). Qed.
Lemma lem8133866 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term20 A B P p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8133865 A B P t p lt2 s a f g h1 h2 h3) (@lem8132125 A B P f t g a h1)). Qed.
Lemma lem8133867 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term20 A B P p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : (term102 A B P f t g a) = False.
Proof. exact (prop_ext (fun h4 : term102 A B P f t g a => @lem8133866 A B P t p lt2 s a f g h1 h2 h3) (fun h4 : False => @lem8131625 A B P f t g a h1)). Qed.
Lemma lem8133868 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term102 A B P f t g a) (h2 : term20 A B P p lt2 t s) (h3 : term90 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8133867 A B P t p lt2 s a f g h1 h2 h3) (@lem8131625 A B P f t g a h1)). Qed.
Lemma lem8133869 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term20 A B P p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : term101 A B P f t g a.
Proof. exact (fun h0 : term102 A B P f t g a => @lem8133868 A B P t p lt2 s a f g h0 h1 h2). Qed.
Lemma lem8133870 {A B P : Type'} (t : type557 A B P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term20 A B P p lt2 t s) (h2 : term90 A B P p lt2 s a f g) : (term39 A B P t f a) = (term39 A B P t g a).
Proof. exact (EQ_MP (@lem8131624 A B P f t g a) (@lem8133869 A B P t p lt2 s a f g h1 h2)). Qed.
Lemma lem8133871 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term20 A B P p lt2 t s) : term47 A B P p lt2 s f t g a.
Proof. exact (fun h0 : term90 A B P p lt2 s a f g => @lem8133870 A B P t p lt2 s a f g h1 h0). Qed.
Lemma lem8133876 {A B P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term20 A B P p lt2 t s) : term51 A B P p lt2 s f t g.
Proof. exact (fun a : P => @lem8133871 A B P f g a p lt2 t s h1). Qed.
Lemma lem8133881 {A B P : Type'} (f : A -> B) (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term20 A B P p lt2 t s) : term55 A B P p lt2 s f t.
Proof. exact (fun g : A -> B => @lem8133876 A B P f g p lt2 t s h1). Qed.
Lemma lem8133886 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : type557 A B P) (s : P -> A) (h1 : term20 A B P p lt2 t s) : term58 A B P p lt2 s t.
Proof. exact (fun f : A -> B => @lem8133881 A B P f p lt2 t s h1). Qed.
Lemma lem8133887 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type557 A B P) : term60 A B P p lt2 s t.
Proof. exact (fun h0 : term20 A B P p lt2 t s => @lem8133886 A B P p lt2 t s h0). Qed.
Lemma lem8133892 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : term64 A B P p lt2 s.
Proof. exact (fun t : type557 A B P => @lem8133887 A B P p lt2 s t). Qed.
Lemma lem8133897 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : term68 A B P p lt2.
Proof. exact (fun s : P -> A => @lem8133892 A B P p lt2 s). Qed.
Lemma lem8133902 {A B P : Type'} (lt2 : type1402 A) : term72 A B P lt2.
Proof. exact (fun p : type560 A B P => @lem8133897 A B P p lt2). Qed.
Lemma lem8133907 {A B P : Type'} : term76 A B P.
Proof. exact (fun lt2 : type1402 A => @lem8133902 A B P lt2). Qed.
Lemma lem8133908 {A B P : Type'} : term78 A B P.
Proof. exact (EQ_MP (@lem8131618 A B P) (@lem8133907 A B P)). Qed.
Lemma lem8133910 {A B P : Type'} : term78 A B P.
Proof. exact (@lem8131332 A B P (@lem8133908 A B P)). Qed.
Lemma lem8133911 {A B P : Type'} (h1 : term79 A B P) : False.
Proof. exact (@lem8133910 A B P (@lem8131316 A B P h1)). Qed.
Lemma lem8133912 {A B P : Type'} (h1 : term79 A B P) : (term79 A B P) = False.
Proof. exact (prop_ext (fun h2 : term79 A B P => @lem8133911 A B P h1) (fun h2 : False => @lem8131316 A B P h1)). Qed.
Lemma lem8133913 {A B P : Type'} (h1 : term79 A B P) : False.
Proof. exact (EQ_MP (@lem8133912 A B P h1) (@lem8131316 A B P h1)). Qed.
Lemma lem8133914 {A B P : Type'} : term78 A B P.
Proof. exact (fun h0 : term79 A B P => @lem8133913 A B P h0). Qed.
Lemma lem8133915 {A B P : Type'} : term76 A B P.
Proof. exact (EQ_MP (@lem8131315 A B P) (@lem8133914 A B P)). Qed.
Lemma lem8133916 {A B P : Type'} : term75 A B P.
Proof. exact (EQ_MP (@lem8131311 A B P) (@lem8133915 A B P)). Qed.
