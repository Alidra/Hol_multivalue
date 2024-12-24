Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_LAMBDA_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import FUN_EQ_THM_spec.
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
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
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
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Lemma lem8126037 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8126038 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8126039 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8126038 t1) (@lem8126037 t1)). Qed.
Lemma lem8126040 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8126039 t1 t2). Qed.
Lemma lem8126041 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8126042 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8126041 t1 t2) (@lem8126040 t1 t2)). Qed.
Lemma lem8126043 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8126042 t1 t2 t3). Qed.
Lemma lem8126044 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8126045 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8126044 t1 t2 t3) (@lem8126043 t1 t2 t3)). Qed.
Lemma lem8126046 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8126045 t1 t2 t3)). Qed.
Lemma lem8126047 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term7 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem8126048 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term7 _5106 _5107 P) = ((term8 _5106 _5107 P) = (term9 _5106 _5107 P)).
Proof. exact (eq_refl (term7 _5106 _5107 P)). Qed.
Lemma lem8126050 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem8126051 {A B : Type'} (f : A -> B) : (term10 A B f) = (term11 A B f).
Proof. exact (eq_refl (term10 A B f)). Qed.
Lemma lem8126052 {A B : Type'} (f : A -> B) : term11 A B f.
Proof. exact (EQ_MP (@lem8126051 A B f) (@lem8126050 A B f)). Qed.
Lemma lem8126053 {A B : Type'} (f : A -> B) (g : A -> B) : term12 A B f g.
Proof. exact (@lem8126052 A B f g). Qed.
Lemma lem8126054 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = ((f = g) = (term13 A B f g)).
Proof. exact (eq_refl (term12 A B f g)). Qed.
Lemma lem8126056 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term14 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8126057 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term14 _143449 _143452 _143456 _143457 _143462 p) = (term15 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term14 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8126058 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term15 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8126057 _143449 _143452 _143456 _143457 _143462 p) (@lem8126056 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8126059 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term16 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8126058 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8126060 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term16 _143449 _143452 _143456 _143457 _143462 p lt2) = (term17 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term16 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8126061 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term17 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8126060 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8126059 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8126062 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term18 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8126061 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8126063 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term18 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term19 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term18 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8126064 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term19 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8126063 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8126062 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8126065 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term20 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8126064 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8126066 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term20 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term21 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term20 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8126095 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term21 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8126066 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8126065 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8126096 {A B C P : Type'} (p : type541 A B C P) (lt2 : type1402 A) (s : type1224 A C P) (t : type541 A B C P) : (@admissible A B A Prop (prod C P) lt2 p s t) = (term22 A B C P p lt2 s t).
Proof. exact (@lem8126095 A B A Prop (prod C P) p lt2 s t). Qed.
Lemma lem8126097 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term23 A B C P lt2 p s t) = (term24 A B C P p lt2 s t).
Proof. exact (@lem8126096 A B C P (term25 A B C P p) lt2 (term26 A C P s) (term27 A B C P t)). Qed.
Lemma lem8126115 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term8 _5106 _5107 P) = (term9 _5106 _5107 P).
Proof. exact (EQ_MP (@lem8126048 _5106 _5107 P) (@lem8126047 _5106 _5107 P)). Qed.
Lemma lem8126116 {C P : Type'} (P' : type1210 C P) : (term28 C P P') = (term29 C P P').
Proof. exact (@lem8126115 P C P'). Qed.
Lemma lem8126117 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term30 A B C P p lt2 s f t g) = (term31 A B C P p lt2 s f t g).
Proof. exact (@lem8126116 C P (term32 A B C P p lt2 s f t g)). Qed.
Lemma lem8126118 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : prod C P) : (term33 A B C P p lt2 s f t g a) = (term34 A B C P p lt2 s f t g a).
Proof. exact (eq_refl (term33 A B C P p lt2 s f t g a)). Qed.
Lemma lem8126119 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term35 A B C P p lt2 s f t g) = (term32 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun a : prod C P => @lem8126118 A B C P p lt2 s f t g a)). Qed.
Lemma lem8126120 {C P : Type'} : (@all (prod C P)) = (@all (prod C P)).
Proof. exact (eq_refl (@all (prod C P))). Qed.
Lemma lem8126121 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term30 A B C P p lt2 s f t g) = (term36 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8126120 C P) (@lem8126119 A B C P p lt2 s f t g)). Qed.
Lemma lem8126122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126123 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term37 A B C P p lt2 s f t g) = (term38 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8126122) (@lem8126121 A B C P p lt2 s f t g)). Qed.
Lemma lem8126124 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term39 A B C P p lt2 s f t g p1 p2) = (term40 A B C P p lt2 s f t g p1 p2).
Proof. exact (eq_refl (term39 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8126125 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term41 A B C P p lt2 s f t g p1) = (term42 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8126124 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8126126 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8126127 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term43 A B C P p lt2 s f t g p1) = (term44 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8126126 P) (@lem8126125 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8126128 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term45 A B C P p lt2 s f t g) = (term46 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8126127 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8126129 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8126130 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term31 A B C P p lt2 s f t g) = (term47 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8126129 C) (@lem8126128 A B C P p lt2 s f t g)). Qed.
Lemma lem8126131 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : ((term30 A B C P p lt2 s f t g) = (term31 A B C P p lt2 s f t g)) = ((term36 A B C P p lt2 s f t g) = (term47 A B C P p lt2 s f t g)).
Proof. exact (MK_COMB (@lem8126123 A B C P p lt2 s f t g) (@lem8126130 A B C P p lt2 s f t g)). Qed.
Lemma lem8126132 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term36 A B C P p lt2 s f t g) = (term47 A B C P p lt2 s f t g).
Proof. exact (EQ_MP (@lem8126131 A B C P p lt2 s f t g) (@lem8126117 A B C P p lt2 s f t g)). Qed.
Lemma lem8126150 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126151 {A B C P : Type'} (f : type541 A B C P) (y : A -> B) : (term49 A B C P f y) = (f y).
Proof. exact (@lem8126150 (A -> B) (type1210 C P) f y). Qed.
Lemma lem8126152 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term50 A B C P p f) = (term51 A B C P p f).
Proof. exact (@lem8126151 A B C P (term25 A B C P p) f). Qed.
Lemma lem8126153 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term51 A B C P p f) = (term52 A B C P p f).
Proof. exact (eq_refl (term51 A B C P p f)). Qed.
Lemma lem8126154 {A B C P : Type'} (p : type560 A B P) : (term53 A B C P p) = (term25 A B C P p).
Proof. exact (fun_ext (fun f : A -> B => @lem8126153 A B C P p f)). Qed.
Lemma lem8126155 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8126156 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term50 A B C P p f) = (term51 A B C P p f).
Proof. exact (MK_COMB (@lem8126154 A B C P p) (@lem8126155 A B f)). Qed.
Lemma lem8126157 {C P : Type'} : (@eq ((prod C P) -> Prop)) = (@eq ((prod C P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod C P) -> Prop))). Qed.
Lemma lem8126158 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term54 A B C P p f) = (term55 A B C P p f).
Proof. exact (MK_COMB (@lem8126157 C P) (@lem8126156 A B C P p f)). Qed.
Lemma lem8126159 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term51 A B C P p f) = (term52 A B C P p f).
Proof. exact (eq_refl (term51 A B C P p f)). Qed.
Lemma lem8126160 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : ((term50 A B C P p f) = (term51 A B C P p f)) = ((term51 A B C P p f) = (term52 A B C P p f)).
Proof. exact (MK_COMB (@lem8126158 A B C P p f) (@lem8126159 A B C P p f)). Qed.
Lemma lem8126161 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term51 A B C P p f) = (term52 A B C P p f).
Proof. exact (EQ_MP (@lem8126160 A B C P p f) (@lem8126152 A B C P p f)). Qed.
Lemma lem8126174 {C P : Type'} (p1 : C) (p2 : P) : (@pair C P p1 p2) = (@pair C P p1 p2).
Proof. exact (eq_refl (@pair C P p1 p2)). Qed.
Lemma lem8126175 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (p1 : C) (p2 : P) : (term56 A B C P p f p1 p2) = (term57 A B C P p f p1 p2).
Proof. exact (MK_COMB (@lem8126161 A B C P p f) (@lem8126174 C P p1 p2)). Qed.
Lemma lem8126176 {C P : Type'} (a0 : C) (a1 : P) : a0 = (term58 C P a0 a1).
Proof. exact (@lem51128 C P a0 a1). Qed.
Lemma lem8126177 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (@lem8126176 C P u x). Qed.
Lemma lem8126178 {C P : Type'} (a0 : C) (a1 : P) : a1 = (term59 C P a0 a1).
Proof. exact (@lem51159 C P a0 a1). Qed.
Lemma lem8126179 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (@lem8126178 C P u x). Qed.
Lemma lem8126180 {C : Type'} (u : C) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem8126181 {C : Type'} : (term60 C) = (term60 C).
Proof. exact (eq_refl (term60 C)). Qed.
Lemma lem8126182 {C P : Type'} (u : C) (x : P) : (term61 C u) = (term62 C P u x).
Proof. exact (MK_COMB (@lem8126181 C) (@lem8126177 C P u x)). Qed.
Lemma lem8126183 {C P : Type'} (u : C) (x : P) : (term62 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term62 C P u x)). Qed.
Lemma lem8126184 {C : Type'} (u : C) : (term63 C u) = (term63 C u).
Proof. exact (eq_refl (term63 C u)). Qed.
Lemma lem8126185 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = ((term61 C u) = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126184 C u) (@lem8126183 C P u x)). Qed.
Lemma lem8126186 {C : Type'} (u : C) : (term61 C u) = u.
Proof. exact (eq_refl (term61 C u)). Qed.
Lemma lem8126187 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8126188 {C : Type'} (u : C) : (term63 C u) = (@eq C u).
Proof. exact (MK_COMB (@lem8126187 C) (@lem8126186 C u)). Qed.
Lemma lem8126189 {C P : Type'} (u : C) (x : P) : (term58 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term58 C P u x)). Qed.
Lemma lem8126190 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term58 C P u x)) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126188 C u) (@lem8126189 C P u x)). Qed.
Lemma lem8126191 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = (u = (term58 C P u x)).
Proof. exact (TRANS (@lem8126185 C P u x) (@lem8126190 C P u x)). Qed.
Lemma lem8126192 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126191 C P u x) (@lem8126182 C P u x)). Qed.
Lemma lem8126193 {C : Type'} (u : C) : (@eq C u) = (@eq C u).
Proof. exact (eq_refl (@eq C u)). Qed.
Lemma lem8126194 {C P : Type'} (u : C) (x : P) : (u = u) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126193 C u) (@lem8126192 C P u x)). Qed.
Lemma lem8126195 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126194 C P u x) (@lem8126180 C u)). Qed.
Lemma lem8126196 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126197 {P : Type'} : (term60 P) = (term60 P).
Proof. exact (eq_refl (term60 P)). Qed.
Lemma lem8126198 {C P : Type'} (u : C) (x : P) : (term61 P x) = (term64 C P u x).
Proof. exact (MK_COMB (@lem8126197 P) (@lem8126179 C P u x)). Qed.
Lemma lem8126199 {C P : Type'} (u : C) (x : P) : (term64 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term64 C P u x)). Qed.
Lemma lem8126200 {P : Type'} (x : P) : (term63 P x) = (term63 P x).
Proof. exact (eq_refl (term63 P x)). Qed.
Lemma lem8126201 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = ((term61 P x) = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126200 P x) (@lem8126199 C P u x)). Qed.
Lemma lem8126202 {P : Type'} (x : P) : (term61 P x) = x.
Proof. exact (eq_refl (term61 P x)). Qed.
Lemma lem8126203 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8126204 {P : Type'} (x : P) : (term63 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8126203 P) (@lem8126202 P x)). Qed.
Lemma lem8126205 {C P : Type'} (u : C) (x : P) : (term59 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term59 C P u x)). Qed.
Lemma lem8126206 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term59 C P u x)) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126204 P x) (@lem8126205 C P u x)). Qed.
Lemma lem8126207 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = (x = (term59 C P u x)).
Proof. exact (TRANS (@lem8126201 C P u x) (@lem8126206 C P u x)). Qed.
Lemma lem8126208 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126207 C P u x) (@lem8126198 C P u x)). Qed.
Lemma lem8126209 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8126210 {C P : Type'} (u : C) (x : P) : (x = x) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126209 P x) (@lem8126208 C P u x)). Qed.
Lemma lem8126211 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126210 C P u x) (@lem8126196 P x)). Qed.
Lemma lem8126212 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term65 A B C P p f) = (term65 A B C P p f).
Proof. exact (eq_refl (term65 A B C P p f)). Qed.
Lemma lem8126213 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : (term66 A B C P p f u) = (term67 A B C P p f u x).
Proof. exact (MK_COMB (@lem8126212 A B C P p f) (@lem8126195 C P u x)). Qed.
Lemma lem8126214 {A B C P : Type'} (u : C) (x : P) (p : type560 A B P) (f : A -> B) : (term67 A B C P p f u x) = (term68 A B P p f).
Proof. exact (eq_refl (term67 A B C P p f u x)). Qed.
Lemma lem8126215 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) : (term69 A B C P p f u) = (term69 A B C P p f u).
Proof. exact (eq_refl (term69 A B C P p f u)). Qed.
Lemma lem8126216 {A B C P : Type'} (x : P) (u : C) (p : type560 A B P) (f : A -> B) : ((term66 A B C P p f u) = (term67 A B C P p f u x)) = ((term66 A B C P p f u) = (term68 A B P p f)).
Proof. exact (MK_COMB (@lem8126215 A B C P p f u) (@lem8126214 A B C P u x p f)). Qed.
Lemma lem8126217 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) : (term66 A B C P p f u) = (term68 A B P p f).
Proof. exact (eq_refl (term66 A B C P p f u)). Qed.
Lemma lem8126218 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8126219 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) : (term69 A B C P p f u) = (term70 A B P p f).
Proof. exact (MK_COMB (@lem8126218 P) (@lem8126217 A B C P u p f)). Qed.
Lemma lem8126220 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (term68 A B P p f) = (term68 A B P p f).
Proof. exact (eq_refl (term68 A B P p f)). Qed.
Lemma lem8126221 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) : ((term66 A B C P p f u) = (term68 A B P p f)) = ((term68 A B P p f) = (term68 A B P p f)).
Proof. exact (MK_COMB (@lem8126219 A B C P u p f) (@lem8126220 A B P p f)). Qed.
Lemma lem8126222 {A B C P : Type'} (u : C) (x : P) (p : type560 A B P) (f : A -> B) : ((term66 A B C P p f u) = (term67 A B C P p f u x)) = ((term68 A B P p f) = (term68 A B P p f)).
Proof. exact (TRANS (@lem8126216 A B C P x u p f) (@lem8126221 A B C P u p f)). Qed.
Lemma lem8126223 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (term68 A B P p f) = (term68 A B P p f).
Proof. exact (EQ_MP (@lem8126222 A B Prop P (@el Prop) (@el P) p f) (@lem8126213 A B Prop P p f (@el Prop) (@el P))). Qed.
Lemma lem8126224 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : (term71 A B P p f x) = (term72 A B C P p f u x).
Proof. exact (MK_COMB (@lem8126223 A B P p f) (@lem8126211 C P u x)). Qed.
Lemma lem8126225 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : (term72 A B C P p f u x) = (term73 A B C P p f u x).
Proof. exact (eq_refl (term72 A B C P p f u x)). Qed.
Lemma lem8126226 {A B P : Type'} (p : type560 A B P) (f : A -> B) (x : P) : (term74 A B P p f x) = (term74 A B P p f x).
Proof. exact (eq_refl (term74 A B P p f x)). Qed.
Lemma lem8126227 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : ((term71 A B P p f x) = (term72 A B C P p f u x)) = ((term71 A B P p f x) = (term73 A B C P p f u x)).
Proof. exact (MK_COMB (@lem8126226 A B P p f x) (@lem8126225 A B C P p f u x)). Qed.
Lemma lem8126228 {A B P : Type'} (p : type560 A B P) (f : A -> B) (x : P) : (term71 A B P p f x) = (p f x).
Proof. exact (eq_refl (term71 A B P p f x)). Qed.
Lemma lem8126229 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126230 {A B P : Type'} (p : type560 A B P) (f : A -> B) (x : P) : (term74 A B P p f x) = (term75 A B P p f x).
Proof. exact (MK_COMB (@lem8126229) (@lem8126228 A B P p f x)). Qed.
Lemma lem8126231 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : (term73 A B C P p f u x) = (term73 A B C P p f u x).
Proof. exact (eq_refl (term73 A B C P p f u x)). Qed.
Lemma lem8126232 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : ((term71 A B P p f x) = (term73 A B C P p f u x)) = ((p f x) = (term73 A B C P p f u x)).
Proof. exact (MK_COMB (@lem8126230 A B P p f x) (@lem8126231 A B C P p f u x)). Qed.
Lemma lem8126233 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : ((term71 A B P p f x) = (term72 A B C P p f u x)) = ((p f x) = (term73 A B C P p f u x)).
Proof. exact (TRANS (@lem8126227 A B C P p f u x) (@lem8126232 A B C P p f u x)). Qed.
Lemma lem8126234 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : (p f x) = (term73 A B C P p f u x).
Proof. exact (EQ_MP (@lem8126233 A B C P p f u x) (@lem8126224 A B C P p f u x)). Qed.
Lemma lem8126235 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : (term73 A B C P p f u x) = (p f x).
Proof. exact (SYM (@lem8126234 A B C P p f u x)). Qed.
Lemma lem8126236 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) (x : P) : (term76 A B C P p f u x) = (term73 A B C P p f u x).
Proof. exact (eq_refl (term76 A B C P p f u x)). Qed.
Lemma lem8126237 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : (term76 A B C P p f u x) = (p f x).
Proof. exact (TRANS (@lem8126236 A B C P p f u x) (@lem8126235 A B C P u p f x)). Qed.
Lemma lem8126238 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) : term77 A B C P u p f.
Proof. exact (fun x : P => @lem8126237 A B C P u p f x). Qed.
Lemma lem8126239 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : term78 A B C P p f.
Proof. exact (fun u : C => @lem8126238 A B C P u p f). Qed.
Lemma lem8126240 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : term79 A B C P p f.
Proof. exact (ex_intro (term80 A B C P p f) (term81 A B C P p f) (@lem8126239 A B C P p f)). Qed.
Lemma lem8126242 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8126243 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8126242 Prop a b). Qed.
Lemma lem8126244 {A B C P : Type'} (_107578 : type1210 C P) (u : C) (p : type560 A B P) (f : A -> B) (x : P) : ((term82 C P _107578 u x) = (p f x)) = (term83 A B C P _107578 u p f x).
Proof. exact (@lem8126243 (term82 C P _107578 u x) (p f x)). Qed.
Lemma lem8126245 {A B C P : Type'} (_107578 : type1210 C P) (u : C) (p : type560 A B P) (f : A -> B) : (term84 A B C P _107578 u p f) = (term85 A B C P _107578 u p f).
Proof. exact (fun_ext (fun x : P => @lem8126244 A B C P _107578 u p f x)). Qed.
Lemma lem8126246 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8126247 {A B C P : Type'} (_107578 : type1210 C P) (u : C) (p : type560 A B P) (f : A -> B) : (term86 A B C P _107578 u p f) = (term87 A B C P _107578 u p f).
Proof. exact (MK_COMB (@lem8126246 P) (@lem8126245 A B C P _107578 u p f)). Qed.
Lemma lem8126248 {A B C P : Type'} (_107578 : type1210 C P) (p : type560 A B P) (f : A -> B) : (term88 A B C P _107578 p f) = (term89 A B C P _107578 p f).
Proof. exact (fun_ext (fun u : C => @lem8126247 A B C P _107578 u p f)). Qed.
Lemma lem8126249 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8126250 {A B C P : Type'} (_107578 : type1210 C P) (p : type560 A B P) (f : A -> B) : (term90 A B C P _107578 p f) = (term91 A B C P _107578 p f).
Proof. exact (MK_COMB (@lem8126249 C) (@lem8126248 A B C P _107578 p f)). Qed.
Lemma lem8126251 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term80 A B C P p f) = (term92 A B C P p f).
Proof. exact (fun_ext (fun _107578 : type1210 C P => @lem8126250 A B C P _107578 p f)). Qed.
Lemma lem8126252 {C P : Type'} : (@ex ((prod C P) -> Prop)) = (@ex ((prod C P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod C P) -> Prop))). Qed.
Lemma lem8126253 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term79 A B C P p f) = (term93 A B C P p f).
Proof. exact (MK_COMB (@lem8126252 C P) (@lem8126251 A B C P p f)). Qed.
Lemma lem8126254 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : term93 A B C P p f.
Proof. exact (EQ_MP (@lem8126253 A B C P p f) (@lem8126240 A B C P p f)). Qed.
Lemma lem8126256 {_5076 : Type'} (P : _5076 -> Prop) : term94 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8126257 {C P : Type'} (P' : type324 C P) : term95 C P P'.
Proof. exact (@lem8126256 (type1210 C P) P'). Qed.
Lemma lem8126258 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : term96 A B C P p f.
Proof. exact (@lem8126257 C P (term92 A B C P p f)). Qed.
Lemma lem8126259 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : term97 A B C P p f.
Proof. exact (@lem8126258 A B C P p f (@lem8126254 A B C P p f)). Qed.
Lemma lem8126260 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term97 A B C P p f) = (term98 A B C P p f).
Proof. exact (eq_refl (term97 A B C P p f)). Qed.
Lemma lem8126261 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : term98 A B C P p f.
Proof. exact (EQ_MP (@lem8126260 A B C P p f) (@lem8126259 A B C P p f)). Qed.
Lemma lem8126262 {A B C P : Type'} (p : type560 A B P) (f : A -> B) (u : C) : term99 A B C P p f u.
Proof. exact (@lem8126261 A B C P p f u). Qed.
Lemma lem8126263 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) : (term99 A B C P p f u) = (term100 A B C P u p f).
Proof. exact (eq_refl (term99 A B C P p f u)). Qed.
Lemma lem8126264 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) : term100 A B C P u p f.
Proof. exact (EQ_MP (@lem8126263 A B C P u p f) (@lem8126262 A B C P p f u)). Qed.
Lemma lem8126265 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : term101 A B C P u p f x.
Proof. exact (@lem8126264 A B C P u p f x). Qed.
Lemma lem8126266 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : (term101 A B C P u p f x) = (term102 A B C P u p f x).
Proof. exact (eq_refl (term101 A B C P u p f x)). Qed.
Lemma lem8126267 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : term102 A B C P u p f x.
Proof. exact (EQ_MP (@lem8126266 A B C P u p f x) (@lem8126265 A B C P u p f x)). Qed.
Lemma lem8126269 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8126270 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8126269 Prop a b). Qed.
Lemma lem8126271 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : (term102 A B C P u p f x) = ((term57 A B C P p f u x) = (p f x)).
Proof. exact (@lem8126270 (term57 A B C P p f u x) (p f x)). Qed.
Lemma lem8126272 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : (term57 A B C P p f u x) = (p f x).
Proof. exact (EQ_MP (@lem8126271 A B C P u p f x) (@lem8126267 A B C P u p f x)). Qed.
Lemma lem8126273 {A B C P : Type'} (u : C) (p : type560 A B P) (f : A -> B) (x : P) : (term57 A B C P p f u x) = (p f x).
Proof. exact (@lem8126272 A B C P u p f x). Qed.
Lemma lem8126274 {A B C P : Type'} (p1 : C) (p : type560 A B P) (f : A -> B) (p2 : P) : (term57 A B C P p f p1 p2) = (p f p2).
Proof. exact (@lem8126273 A B C P p1 p f p2). Qed.
Lemma lem8126275 {A B C P : Type'} (p1 : C) (p : type560 A B P) (f : A -> B) (p2 : P) : (term56 A B C P p f p1 p2) = (p f p2).
Proof. exact (TRANS (@lem8126175 A B C P p f p1 p2) (@lem8126274 A B C P p1 p f p2)). Qed.
Lemma lem8126276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8126277 {A B C P : Type'} (p1 : C) (p : type560 A B P) (f : A -> B) (p2 : P) : (term103 A B C P p f p1 p2) = (term104 A B P p f p2).
Proof. exact (MK_COMB (@lem8126276) (@lem8126275 A B C P p1 p f p2)). Qed.
Lemma lem8126281 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126282 {A B C P : Type'} (f : type541 A B C P) (y : A -> B) : (term49 A B C P f y) = (f y).
Proof. exact (@lem8126281 (A -> B) (type1210 C P) f y). Qed.
Lemma lem8126283 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term50 A B C P p g) = (term51 A B C P p g).
Proof. exact (@lem8126282 A B C P (term25 A B C P p) g). Qed.
Lemma lem8126284 {A B C P : Type'} (p : type560 A B P) (f : A -> B) : (term51 A B C P p f) = (term52 A B C P p f).
Proof. exact (eq_refl (term51 A B C P p f)). Qed.
Lemma lem8126285 {A B C P : Type'} (p : type560 A B P) : (term53 A B C P p) = (term25 A B C P p).
Proof. exact (fun_ext (fun f : A -> B => @lem8126284 A B C P p f)). Qed.
Lemma lem8126286 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8126287 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term50 A B C P p g) = (term51 A B C P p g).
Proof. exact (MK_COMB (@lem8126285 A B C P p) (@lem8126286 A B g)). Qed.
Lemma lem8126288 {C P : Type'} : (@eq ((prod C P) -> Prop)) = (@eq ((prod C P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod C P) -> Prop))). Qed.
Lemma lem8126289 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term54 A B C P p g) = (term55 A B C P p g).
Proof. exact (MK_COMB (@lem8126288 C P) (@lem8126287 A B C P p g)). Qed.
Lemma lem8126290 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term51 A B C P p g) = (term52 A B C P p g).
Proof. exact (eq_refl (term51 A B C P p g)). Qed.
Lemma lem8126291 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : ((term50 A B C P p g) = (term51 A B C P p g)) = ((term51 A B C P p g) = (term52 A B C P p g)).
Proof. exact (MK_COMB (@lem8126289 A B C P p g) (@lem8126290 A B C P p g)). Qed.
Lemma lem8126292 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term51 A B C P p g) = (term52 A B C P p g).
Proof. exact (EQ_MP (@lem8126291 A B C P p g) (@lem8126283 A B C P p g)). Qed.
Lemma lem8126305 {C P : Type'} (p1 : C) (p2 : P) : (@pair C P p1 p2) = (@pair C P p1 p2).
Proof. exact (eq_refl (@pair C P p1 p2)). Qed.
Lemma lem8126306 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (p1 : C) (p2 : P) : (term56 A B C P p g p1 p2) = (term57 A B C P p g p1 p2).
Proof. exact (MK_COMB (@lem8126292 A B C P p g) (@lem8126305 C P p1 p2)). Qed.
Lemma lem8126307 {C P : Type'} (a0 : C) (a1 : P) : a0 = (term58 C P a0 a1).
Proof. exact (@lem51128 C P a0 a1). Qed.
Lemma lem8126308 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (@lem8126307 C P u x). Qed.
Lemma lem8126309 {C P : Type'} (a0 : C) (a1 : P) : a1 = (term59 C P a0 a1).
Proof. exact (@lem51159 C P a0 a1). Qed.
Lemma lem8126310 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (@lem8126309 C P u x). Qed.
Lemma lem8126311 {C : Type'} (u : C) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem8126312 {C : Type'} : (term60 C) = (term60 C).
Proof. exact (eq_refl (term60 C)). Qed.
Lemma lem8126313 {C P : Type'} (u : C) (x : P) : (term61 C u) = (term62 C P u x).
Proof. exact (MK_COMB (@lem8126312 C) (@lem8126308 C P u x)). Qed.
Lemma lem8126314 {C P : Type'} (u : C) (x : P) : (term62 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term62 C P u x)). Qed.
Lemma lem8126315 {C : Type'} (u : C) : (term63 C u) = (term63 C u).
Proof. exact (eq_refl (term63 C u)). Qed.
Lemma lem8126316 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = ((term61 C u) = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126315 C u) (@lem8126314 C P u x)). Qed.
Lemma lem8126317 {C : Type'} (u : C) : (term61 C u) = u.
Proof. exact (eq_refl (term61 C u)). Qed.
Lemma lem8126318 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8126319 {C : Type'} (u : C) : (term63 C u) = (@eq C u).
Proof. exact (MK_COMB (@lem8126318 C) (@lem8126317 C u)). Qed.
Lemma lem8126320 {C P : Type'} (u : C) (x : P) : (term58 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term58 C P u x)). Qed.
Lemma lem8126321 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term58 C P u x)) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126319 C u) (@lem8126320 C P u x)). Qed.
Lemma lem8126322 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = (u = (term58 C P u x)).
Proof. exact (TRANS (@lem8126316 C P u x) (@lem8126321 C P u x)). Qed.
Lemma lem8126323 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126322 C P u x) (@lem8126313 C P u x)). Qed.
Lemma lem8126324 {C : Type'} (u : C) : (@eq C u) = (@eq C u).
Proof. exact (eq_refl (@eq C u)). Qed.
Lemma lem8126325 {C P : Type'} (u : C) (x : P) : (u = u) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126324 C u) (@lem8126323 C P u x)). Qed.
Lemma lem8126326 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126325 C P u x) (@lem8126311 C u)). Qed.
Lemma lem8126327 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126328 {P : Type'} : (term60 P) = (term60 P).
Proof. exact (eq_refl (term60 P)). Qed.
Lemma lem8126329 {C P : Type'} (u : C) (x : P) : (term61 P x) = (term64 C P u x).
Proof. exact (MK_COMB (@lem8126328 P) (@lem8126310 C P u x)). Qed.
Lemma lem8126330 {C P : Type'} (u : C) (x : P) : (term64 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term64 C P u x)). Qed.
Lemma lem8126331 {P : Type'} (x : P) : (term63 P x) = (term63 P x).
Proof. exact (eq_refl (term63 P x)). Qed.
Lemma lem8126332 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = ((term61 P x) = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126331 P x) (@lem8126330 C P u x)). Qed.
Lemma lem8126333 {P : Type'} (x : P) : (term61 P x) = x.
Proof. exact (eq_refl (term61 P x)). Qed.
Lemma lem8126334 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8126335 {P : Type'} (x : P) : (term63 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8126334 P) (@lem8126333 P x)). Qed.
Lemma lem8126336 {C P : Type'} (u : C) (x : P) : (term59 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term59 C P u x)). Qed.
Lemma lem8126337 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term59 C P u x)) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126335 P x) (@lem8126336 C P u x)). Qed.
Lemma lem8126338 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = (x = (term59 C P u x)).
Proof. exact (TRANS (@lem8126332 C P u x) (@lem8126337 C P u x)). Qed.
Lemma lem8126339 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126338 C P u x) (@lem8126329 C P u x)). Qed.
Lemma lem8126340 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8126341 {C P : Type'} (u : C) (x : P) : (x = x) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126340 P x) (@lem8126339 C P u x)). Qed.
Lemma lem8126342 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126341 C P u x) (@lem8126327 P x)). Qed.
Lemma lem8126343 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term65 A B C P p g) = (term65 A B C P p g).
Proof. exact (eq_refl (term65 A B C P p g)). Qed.
Lemma lem8126344 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : (term66 A B C P p g u) = (term67 A B C P p g u x).
Proof. exact (MK_COMB (@lem8126343 A B C P p g) (@lem8126326 C P u x)). Qed.
Lemma lem8126345 {A B C P : Type'} (u : C) (x : P) (p : type560 A B P) (g : A -> B) : (term67 A B C P p g u x) = (term68 A B P p g).
Proof. exact (eq_refl (term67 A B C P p g u x)). Qed.
Lemma lem8126346 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) : (term69 A B C P p g u) = (term69 A B C P p g u).
Proof. exact (eq_refl (term69 A B C P p g u)). Qed.
Lemma lem8126347 {A B C P : Type'} (x : P) (u : C) (p : type560 A B P) (g : A -> B) : ((term66 A B C P p g u) = (term67 A B C P p g u x)) = ((term66 A B C P p g u) = (term68 A B P p g)).
Proof. exact (MK_COMB (@lem8126346 A B C P p g u) (@lem8126345 A B C P u x p g)). Qed.
Lemma lem8126348 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) : (term66 A B C P p g u) = (term68 A B P p g).
Proof. exact (eq_refl (term66 A B C P p g u)). Qed.
Lemma lem8126349 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8126350 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) : (term69 A B C P p g u) = (term70 A B P p g).
Proof. exact (MK_COMB (@lem8126349 P) (@lem8126348 A B C P u p g)). Qed.
Lemma lem8126351 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (term68 A B P p g) = (term68 A B P p g).
Proof. exact (eq_refl (term68 A B P p g)). Qed.
Lemma lem8126352 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) : ((term66 A B C P p g u) = (term68 A B P p g)) = ((term68 A B P p g) = (term68 A B P p g)).
Proof. exact (MK_COMB (@lem8126350 A B C P u p g) (@lem8126351 A B P p g)). Qed.
Lemma lem8126353 {A B C P : Type'} (u : C) (x : P) (p : type560 A B P) (g : A -> B) : ((term66 A B C P p g u) = (term67 A B C P p g u x)) = ((term68 A B P p g) = (term68 A B P p g)).
Proof. exact (TRANS (@lem8126347 A B C P x u p g) (@lem8126352 A B C P u p g)). Qed.
Lemma lem8126354 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (term68 A B P p g) = (term68 A B P p g).
Proof. exact (EQ_MP (@lem8126353 A B Prop P (@el Prop) (@el P) p g) (@lem8126344 A B Prop P p g (@el Prop) (@el P))). Qed.
Lemma lem8126355 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : (term71 A B P p g x) = (term72 A B C P p g u x).
Proof. exact (MK_COMB (@lem8126354 A B P p g) (@lem8126342 C P u x)). Qed.
Lemma lem8126356 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : (term72 A B C P p g u x) = (term73 A B C P p g u x).
Proof. exact (eq_refl (term72 A B C P p g u x)). Qed.
Lemma lem8126357 {A B P : Type'} (p : type560 A B P) (g : A -> B) (x : P) : (term74 A B P p g x) = (term74 A B P p g x).
Proof. exact (eq_refl (term74 A B P p g x)). Qed.
Lemma lem8126358 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : ((term71 A B P p g x) = (term72 A B C P p g u x)) = ((term71 A B P p g x) = (term73 A B C P p g u x)).
Proof. exact (MK_COMB (@lem8126357 A B P p g x) (@lem8126356 A B C P p g u x)). Qed.
Lemma lem8126359 {A B P : Type'} (p : type560 A B P) (g : A -> B) (x : P) : (term71 A B P p g x) = (p g x).
Proof. exact (eq_refl (term71 A B P p g x)). Qed.
Lemma lem8126360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126361 {A B P : Type'} (p : type560 A B P) (g : A -> B) (x : P) : (term74 A B P p g x) = (term75 A B P p g x).
Proof. exact (MK_COMB (@lem8126360) (@lem8126359 A B P p g x)). Qed.
Lemma lem8126362 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : (term73 A B C P p g u x) = (term73 A B C P p g u x).
Proof. exact (eq_refl (term73 A B C P p g u x)). Qed.
Lemma lem8126363 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : ((term71 A B P p g x) = (term73 A B C P p g u x)) = ((p g x) = (term73 A B C P p g u x)).
Proof. exact (MK_COMB (@lem8126361 A B P p g x) (@lem8126362 A B C P p g u x)). Qed.
Lemma lem8126364 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : ((term71 A B P p g x) = (term72 A B C P p g u x)) = ((p g x) = (term73 A B C P p g u x)).
Proof. exact (TRANS (@lem8126358 A B C P p g u x) (@lem8126363 A B C P p g u x)). Qed.
Lemma lem8126365 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : (p g x) = (term73 A B C P p g u x).
Proof. exact (EQ_MP (@lem8126364 A B C P p g u x) (@lem8126355 A B C P p g u x)). Qed.
Lemma lem8126366 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : (term73 A B C P p g u x) = (p g x).
Proof. exact (SYM (@lem8126365 A B C P p g u x)). Qed.
Lemma lem8126367 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) (x : P) : (term76 A B C P p g u x) = (term73 A B C P p g u x).
Proof. exact (eq_refl (term76 A B C P p g u x)). Qed.
Lemma lem8126368 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : (term76 A B C P p g u x) = (p g x).
Proof. exact (TRANS (@lem8126367 A B C P p g u x) (@lem8126366 A B C P u p g x)). Qed.
Lemma lem8126369 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) : term77 A B C P u p g.
Proof. exact (fun x : P => @lem8126368 A B C P u p g x). Qed.
Lemma lem8126370 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : term78 A B C P p g.
Proof. exact (fun u : C => @lem8126369 A B C P u p g). Qed.
Lemma lem8126371 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : term79 A B C P p g.
Proof. exact (ex_intro (term80 A B C P p g) (term81 A B C P p g) (@lem8126370 A B C P p g)). Qed.
Lemma lem8126373 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8126374 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8126373 Prop a b). Qed.
Lemma lem8126375 {A B C P : Type'} (_107590 : type1210 C P) (u : C) (p : type560 A B P) (g : A -> B) (x : P) : ((term82 C P _107590 u x) = (p g x)) = (term83 A B C P _107590 u p g x).
Proof. exact (@lem8126374 (term82 C P _107590 u x) (p g x)). Qed.
Lemma lem8126376 {A B C P : Type'} (_107590 : type1210 C P) (u : C) (p : type560 A B P) (g : A -> B) : (term84 A B C P _107590 u p g) = (term85 A B C P _107590 u p g).
Proof. exact (fun_ext (fun x : P => @lem8126375 A B C P _107590 u p g x)). Qed.
Lemma lem8126377 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8126378 {A B C P : Type'} (_107590 : type1210 C P) (u : C) (p : type560 A B P) (g : A -> B) : (term86 A B C P _107590 u p g) = (term87 A B C P _107590 u p g).
Proof. exact (MK_COMB (@lem8126377 P) (@lem8126376 A B C P _107590 u p g)). Qed.
Lemma lem8126379 {A B C P : Type'} (_107590 : type1210 C P) (p : type560 A B P) (g : A -> B) : (term88 A B C P _107590 p g) = (term89 A B C P _107590 p g).
Proof. exact (fun_ext (fun u : C => @lem8126378 A B C P _107590 u p g)). Qed.
Lemma lem8126380 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8126381 {A B C P : Type'} (_107590 : type1210 C P) (p : type560 A B P) (g : A -> B) : (term90 A B C P _107590 p g) = (term91 A B C P _107590 p g).
Proof. exact (MK_COMB (@lem8126380 C) (@lem8126379 A B C P _107590 p g)). Qed.
Lemma lem8126382 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term80 A B C P p g) = (term92 A B C P p g).
Proof. exact (fun_ext (fun _107590 : type1210 C P => @lem8126381 A B C P _107590 p g)). Qed.
Lemma lem8126383 {C P : Type'} : (@ex ((prod C P) -> Prop)) = (@ex ((prod C P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod C P) -> Prop))). Qed.
Lemma lem8126384 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term79 A B C P p g) = (term93 A B C P p g).
Proof. exact (MK_COMB (@lem8126383 C P) (@lem8126382 A B C P p g)). Qed.
Lemma lem8126385 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : term93 A B C P p g.
Proof. exact (EQ_MP (@lem8126384 A B C P p g) (@lem8126371 A B C P p g)). Qed.
Lemma lem8126387 {_5076 : Type'} (P : _5076 -> Prop) : term94 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8126388 {C P : Type'} (P' : type324 C P) : term95 C P P'.
Proof. exact (@lem8126387 (type1210 C P) P'). Qed.
Lemma lem8126389 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : term96 A B C P p g.
Proof. exact (@lem8126388 C P (term92 A B C P p g)). Qed.
Lemma lem8126390 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : term97 A B C P p g.
Proof. exact (@lem8126389 A B C P p g (@lem8126385 A B C P p g)). Qed.
Lemma lem8126391 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : (term97 A B C P p g) = (term98 A B C P p g).
Proof. exact (eq_refl (term97 A B C P p g)). Qed.
Lemma lem8126392 {A B C P : Type'} (p : type560 A B P) (g : A -> B) : term98 A B C P p g.
Proof. exact (EQ_MP (@lem8126391 A B C P p g) (@lem8126390 A B C P p g)). Qed.
Lemma lem8126393 {A B C P : Type'} (p : type560 A B P) (g : A -> B) (u : C) : term99 A B C P p g u.
Proof. exact (@lem8126392 A B C P p g u). Qed.
Lemma lem8126394 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) : (term99 A B C P p g u) = (term100 A B C P u p g).
Proof. exact (eq_refl (term99 A B C P p g u)). Qed.
Lemma lem8126395 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) : term100 A B C P u p g.
Proof. exact (EQ_MP (@lem8126394 A B C P u p g) (@lem8126393 A B C P p g u)). Qed.
Lemma lem8126396 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : term101 A B C P u p g x.
Proof. exact (@lem8126395 A B C P u p g x). Qed.
Lemma lem8126397 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : (term101 A B C P u p g x) = (term102 A B C P u p g x).
Proof. exact (eq_refl (term101 A B C P u p g x)). Qed.
Lemma lem8126398 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : term102 A B C P u p g x.
Proof. exact (EQ_MP (@lem8126397 A B C P u p g x) (@lem8126396 A B C P u p g x)). Qed.
Lemma lem8126400 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8126401 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8126400 Prop a b). Qed.
Lemma lem8126402 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : (term102 A B C P u p g x) = ((term57 A B C P p g u x) = (p g x)).
Proof. exact (@lem8126401 (term57 A B C P p g u x) (p g x)). Qed.
Lemma lem8126403 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : (term57 A B C P p g u x) = (p g x).
Proof. exact (EQ_MP (@lem8126402 A B C P u p g x) (@lem8126398 A B C P u p g x)). Qed.
Lemma lem8126404 {A B C P : Type'} (u : C) (p : type560 A B P) (g : A -> B) (x : P) : (term57 A B C P p g u x) = (p g x).
Proof. exact (@lem8126403 A B C P u p g x). Qed.
Lemma lem8126405 {A B C P : Type'} (p1 : C) (p : type560 A B P) (g : A -> B) (p2 : P) : (term57 A B C P p g p1 p2) = (p g p2).
Proof. exact (@lem8126404 A B C P p1 p g p2). Qed.
Lemma lem8126406 {A B C P : Type'} (p1 : C) (p : type560 A B P) (g : A -> B) (p2 : P) : (term56 A B C P p g p1 p2) = (p g p2).
Proof. exact (TRANS (@lem8126306 A B C P p g p1 p2) (@lem8126405 A B C P p1 p g p2)). Qed.
Lemma lem8126407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8126408 {A B C P : Type'} (p1 : C) (p : type560 A B P) (g : A -> B) (p2 : P) : (term103 A B C P p g p1 p2) = (term104 A B P p g p2).
Proof. exact (MK_COMB (@lem8126407) (@lem8126406 A B C P p1 p g p2)). Qed.
Lemma lem8126417 {C P : Type'} (a0 : C) (a1 : P) : a0 = (term58 C P a0 a1).
Proof. exact (@lem51128 C P a0 a1). Qed.
Lemma lem8126418 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (@lem8126417 C P u x). Qed.
Lemma lem8126419 {C P : Type'} (a0 : C) (a1 : P) : a1 = (term59 C P a0 a1).
Proof. exact (@lem51159 C P a0 a1). Qed.
Lemma lem8126420 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (@lem8126419 C P u x). Qed.
Lemma lem8126421 {C : Type'} (u : C) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem8126422 {C : Type'} : (term60 C) = (term60 C).
Proof. exact (eq_refl (term60 C)). Qed.
Lemma lem8126423 {C P : Type'} (u : C) (x : P) : (term61 C u) = (term62 C P u x).
Proof. exact (MK_COMB (@lem8126422 C) (@lem8126418 C P u x)). Qed.
Lemma lem8126424 {C P : Type'} (u : C) (x : P) : (term62 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term62 C P u x)). Qed.
Lemma lem8126425 {C : Type'} (u : C) : (term63 C u) = (term63 C u).
Proof. exact (eq_refl (term63 C u)). Qed.
Lemma lem8126426 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = ((term61 C u) = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126425 C u) (@lem8126424 C P u x)). Qed.
Lemma lem8126427 {C : Type'} (u : C) : (term61 C u) = u.
Proof. exact (eq_refl (term61 C u)). Qed.
Lemma lem8126428 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8126429 {C : Type'} (u : C) : (term63 C u) = (@eq C u).
Proof. exact (MK_COMB (@lem8126428 C) (@lem8126427 C u)). Qed.
Lemma lem8126430 {C P : Type'} (u : C) (x : P) : (term58 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term58 C P u x)). Qed.
Lemma lem8126431 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term58 C P u x)) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126429 C u) (@lem8126430 C P u x)). Qed.
Lemma lem8126432 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = (u = (term58 C P u x)).
Proof. exact (TRANS (@lem8126426 C P u x) (@lem8126431 C P u x)). Qed.
Lemma lem8126433 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126432 C P u x) (@lem8126423 C P u x)). Qed.
Lemma lem8126434 {C : Type'} (u : C) : (@eq C u) = (@eq C u).
Proof. exact (eq_refl (@eq C u)). Qed.
Lemma lem8126435 {C P : Type'} (u : C) (x : P) : (u = u) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126434 C u) (@lem8126433 C P u x)). Qed.
Lemma lem8126436 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126435 C P u x) (@lem8126421 C u)). Qed.
Lemma lem8126437 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126438 {P : Type'} : (term60 P) = (term60 P).
Proof. exact (eq_refl (term60 P)). Qed.
Lemma lem8126439 {C P : Type'} (u : C) (x : P) : (term61 P x) = (term64 C P u x).
Proof. exact (MK_COMB (@lem8126438 P) (@lem8126420 C P u x)). Qed.
Lemma lem8126440 {C P : Type'} (u : C) (x : P) : (term64 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term64 C P u x)). Qed.
Lemma lem8126441 {P : Type'} (x : P) : (term63 P x) = (term63 P x).
Proof. exact (eq_refl (term63 P x)). Qed.
Lemma lem8126442 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = ((term61 P x) = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126441 P x) (@lem8126440 C P u x)). Qed.
Lemma lem8126443 {P : Type'} (x : P) : (term61 P x) = x.
Proof. exact (eq_refl (term61 P x)). Qed.
Lemma lem8126444 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8126445 {P : Type'} (x : P) : (term63 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8126444 P) (@lem8126443 P x)). Qed.
Lemma lem8126446 {C P : Type'} (u : C) (x : P) : (term59 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term59 C P u x)). Qed.
Lemma lem8126447 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term59 C P u x)) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126445 P x) (@lem8126446 C P u x)). Qed.
Lemma lem8126448 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = (x = (term59 C P u x)).
Proof. exact (TRANS (@lem8126442 C P u x) (@lem8126447 C P u x)). Qed.
Lemma lem8126449 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126448 C P u x) (@lem8126439 C P u x)). Qed.
Lemma lem8126450 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8126451 {C P : Type'} (u : C) (x : P) : (x = x) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126450 P x) (@lem8126449 C P u x)). Qed.
Lemma lem8126452 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126451 C P u x) (@lem8126437 P x)). Qed.
Lemma lem8126453 {A C P : Type'} (s : P -> A) : (term105 A C P s) = (term105 A C P s).
Proof. exact (eq_refl (term105 A C P s)). Qed.
Lemma lem8126454 {A C P : Type'} (s : P -> A) (u : C) (x : P) : (term106 A C P s u) = (term107 A C P s u x).
Proof. exact (MK_COMB (@lem8126453 A C P s) (@lem8126436 C P u x)). Qed.
Lemma lem8126455 {A C P : Type'} (u : C) (x : P) (s : P -> A) : (term107 A C P s u x) = (term108 A P s).
Proof. exact (eq_refl (term107 A C P s u x)). Qed.
Lemma lem8126456 {A C P : Type'} (s : P -> A) (u : C) : (term109 A C P s u) = (term109 A C P s u).
Proof. exact (eq_refl (term109 A C P s u)). Qed.
Lemma lem8126457 {A C P : Type'} (x : P) (u : C) (s : P -> A) : ((term106 A C P s u) = (term107 A C P s u x)) = ((term106 A C P s u) = (term108 A P s)).
Proof. exact (MK_COMB (@lem8126456 A C P s u) (@lem8126455 A C P u x s)). Qed.
Lemma lem8126458 {A C P : Type'} (u : C) (s : P -> A) : (term106 A C P s u) = (term108 A P s).
Proof. exact (eq_refl (term106 A C P s u)). Qed.
Lemma lem8126459 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8126460 {A C P : Type'} (u : C) (s : P -> A) : (term109 A C P s u) = (term110 A P s).
Proof. exact (MK_COMB (@lem8126459 A P) (@lem8126458 A C P u s)). Qed.
Lemma lem8126461 {A P : Type'} (s : P -> A) : (term108 A P s) = (term108 A P s).
Proof. exact (eq_refl (term108 A P s)). Qed.
Lemma lem8126462 {A C P : Type'} (u : C) (s : P -> A) : ((term106 A C P s u) = (term108 A P s)) = ((term108 A P s) = (term108 A P s)).
Proof. exact (MK_COMB (@lem8126460 A C P u s) (@lem8126461 A P s)). Qed.
Lemma lem8126463 {A C P : Type'} (u : C) (x : P) (s : P -> A) : ((term106 A C P s u) = (term107 A C P s u x)) = ((term108 A P s) = (term108 A P s)).
Proof. exact (TRANS (@lem8126457 A C P x u s) (@lem8126462 A C P u s)). Qed.
Lemma lem8126464 {A P : Type'} (s : P -> A) : (term108 A P s) = (term108 A P s).
Proof. exact (EQ_MP (@lem8126463 A Prop P (@el Prop) (@el P) s) (@lem8126454 A Prop P s (@el Prop) (@el P))). Qed.
Lemma lem8126465 {A C P : Type'} (s : P -> A) (u : C) (x : P) : (term111 A P s x) = (term112 A C P s u x).
Proof. exact (MK_COMB (@lem8126464 A P s) (@lem8126452 C P u x)). Qed.
Lemma lem8126466 {A C P : Type'} (s : P -> A) (u : C) (x : P) : (term112 A C P s u x) = (term113 A C P s u x).
Proof. exact (eq_refl (term112 A C P s u x)). Qed.
Lemma lem8126467 {A P : Type'} (s : P -> A) (x : P) : (term114 A P s x) = (term114 A P s x).
Proof. exact (eq_refl (term114 A P s x)). Qed.
Lemma lem8126468 {A C P : Type'} (s : P -> A) (u : C) (x : P) : ((term111 A P s x) = (term112 A C P s u x)) = ((term111 A P s x) = (term113 A C P s u x)).
Proof. exact (MK_COMB (@lem8126467 A P s x) (@lem8126466 A C P s u x)). Qed.
Lemma lem8126469 {A P : Type'} (s : P -> A) (x : P) : (term111 A P s x) = (s x).
Proof. exact (eq_refl (term111 A P s x)). Qed.
Lemma lem8126470 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8126471 {A P : Type'} (s : P -> A) (x : P) : (term114 A P s x) = (term115 A P s x).
Proof. exact (MK_COMB (@lem8126470 A) (@lem8126469 A P s x)). Qed.
Lemma lem8126472 {A C P : Type'} (s : P -> A) (u : C) (x : P) : (term113 A C P s u x) = (term113 A C P s u x).
Proof. exact (eq_refl (term113 A C P s u x)). Qed.
Lemma lem8126473 {A C P : Type'} (s : P -> A) (u : C) (x : P) : ((term111 A P s x) = (term113 A C P s u x)) = ((s x) = (term113 A C P s u x)).
Proof. exact (MK_COMB (@lem8126471 A P s x) (@lem8126472 A C P s u x)). Qed.
Lemma lem8126474 {A C P : Type'} (s : P -> A) (u : C) (x : P) : ((term111 A P s x) = (term112 A C P s u x)) = ((s x) = (term113 A C P s u x)).
Proof. exact (TRANS (@lem8126468 A C P s u x) (@lem8126473 A C P s u x)). Qed.
Lemma lem8126475 {A C P : Type'} (s : P -> A) (u : C) (x : P) : (s x) = (term113 A C P s u x).
Proof. exact (EQ_MP (@lem8126474 A C P s u x) (@lem8126465 A C P s u x)). Qed.
Lemma lem8126476 {A C P : Type'} (u : C) (s : P -> A) (x : P) : (term113 A C P s u x) = (s x).
Proof. exact (SYM (@lem8126475 A C P s u x)). Qed.
Lemma lem8126477 {A C P : Type'} (s : P -> A) (u : C) (x : P) : (term116 A C P s u x) = (term113 A C P s u x).
Proof. exact (eq_refl (term116 A C P s u x)). Qed.
Lemma lem8126478 {A C P : Type'} (u : C) (s : P -> A) (x : P) : (term116 A C P s u x) = (s x).
Proof. exact (TRANS (@lem8126477 A C P s u x) (@lem8126476 A C P u s x)). Qed.
Lemma lem8126479 {A C P : Type'} (u : C) (s : P -> A) : term117 A C P u s.
Proof. exact (fun x : P => @lem8126478 A C P u s x). Qed.
Lemma lem8126480 {A C P : Type'} (s : P -> A) : term118 A C P s.
Proof. exact (fun u : C => @lem8126479 A C P u s). Qed.
Lemma lem8126481 {A C P : Type'} (s : P -> A) : term119 A C P s.
Proof. exact (ex_intro (term120 A C P s) (term121 A C P s) (@lem8126480 A C P s)). Qed.
Lemma lem8126483 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8126484 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (@lem8126483 A a b). Qed.
Lemma lem8126485 {A C P : Type'} (_107602 : type1224 A C P) (u : C) (s : P -> A) (x : P) : ((term122 A C P _107602 u x) = (s x)) = (term123 A C P _107602 u s x).
Proof. exact (@lem8126484 A (term122 A C P _107602 u x) (s x)). Qed.
Lemma lem8126486 {A C P : Type'} (_107602 : type1224 A C P) (u : C) (s : P -> A) : (term124 A C P _107602 u s) = (term125 A C P _107602 u s).
Proof. exact (fun_ext (fun x : P => @lem8126485 A C P _107602 u s x)). Qed.
Lemma lem8126487 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8126488 {A C P : Type'} (_107602 : type1224 A C P) (u : C) (s : P -> A) : (term126 A C P _107602 u s) = (term127 A C P _107602 u s).
Proof. exact (MK_COMB (@lem8126487 P) (@lem8126486 A C P _107602 u s)). Qed.
Lemma lem8126489 {A C P : Type'} (_107602 : type1224 A C P) (s : P -> A) : (term128 A C P _107602 s) = (term129 A C P _107602 s).
Proof. exact (fun_ext (fun u : C => @lem8126488 A C P _107602 u s)). Qed.
Lemma lem8126490 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8126491 {A C P : Type'} (_107602 : type1224 A C P) (s : P -> A) : (term130 A C P _107602 s) = (term131 A C P _107602 s).
Proof. exact (MK_COMB (@lem8126490 C) (@lem8126489 A C P _107602 s)). Qed.
Lemma lem8126492 {A C P : Type'} (s : P -> A) : (term120 A C P s) = (term132 A C P s).
Proof. exact (fun_ext (fun _107602 : type1224 A C P => @lem8126491 A C P _107602 s)). Qed.
Lemma lem8126493 {A C P : Type'} : (@ex ((prod C P) -> A)) = (@ex ((prod C P) -> A)).
Proof. exact (eq_refl (@ex ((prod C P) -> A))). Qed.
Lemma lem8126494 {A C P : Type'} (s : P -> A) : (term119 A C P s) = (term133 A C P s).
Proof. exact (MK_COMB (@lem8126493 A C P) (@lem8126492 A C P s)). Qed.
Lemma lem8126495 {A C P : Type'} (s : P -> A) : term133 A C P s.
Proof. exact (EQ_MP (@lem8126494 A C P s) (@lem8126481 A C P s)). Qed.
Lemma lem8126497 {_5076 : Type'} (P : _5076 -> Prop) : term94 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8126498 {A C P : Type'} (P' : type331 A C P) : term134 A C P P'.
Proof. exact (@lem8126497 (type1224 A C P) P'). Qed.
Lemma lem8126499 {A C P : Type'} (s : P -> A) : term135 A C P s.
Proof. exact (@lem8126498 A C P (term132 A C P s)). Qed.
Lemma lem8126500 {A C P : Type'} (s : P -> A) : term136 A C P s.
Proof. exact (@lem8126499 A C P s (@lem8126495 A C P s)). Qed.
Lemma lem8126501 {A C P : Type'} (s : P -> A) : (term136 A C P s) = (term137 A C P s).
Proof. exact (eq_refl (term136 A C P s)). Qed.
Lemma lem8126502 {A C P : Type'} (s : P -> A) : term137 A C P s.
Proof. exact (EQ_MP (@lem8126501 A C P s) (@lem8126500 A C P s)). Qed.
Lemma lem8126503 {A C P : Type'} (s : P -> A) (u : C) : term138 A C P s u.
Proof. exact (@lem8126502 A C P s u). Qed.
Lemma lem8126504 {A C P : Type'} (u : C) (s : P -> A) : (term138 A C P s u) = (term139 A C P u s).
Proof. exact (eq_refl (term138 A C P s u)). Qed.
Lemma lem8126505 {A C P : Type'} (u : C) (s : P -> A) : term139 A C P u s.
Proof. exact (EQ_MP (@lem8126504 A C P u s) (@lem8126503 A C P s u)). Qed.
Lemma lem8126506 {A C P : Type'} (u : C) (s : P -> A) (x : P) : term140 A C P u s x.
Proof. exact (@lem8126505 A C P u s x). Qed.
Lemma lem8126507 {A C P : Type'} (u : C) (s : P -> A) (x : P) : (term140 A C P u s x) = (term141 A C P u s x).
Proof. exact (eq_refl (term140 A C P u s x)). Qed.
Lemma lem8126508 {A C P : Type'} (u : C) (s : P -> A) (x : P) : term141 A C P u s x.
Proof. exact (EQ_MP (@lem8126507 A C P u s x) (@lem8126506 A C P u s x)). Qed.
Lemma lem8126510 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8126511 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (@lem8126510 A a b). Qed.
Lemma lem8126512 {A C P : Type'} (u : C) (s : P -> A) (x : P) : (term141 A C P u s x) = ((term142 A C P s u x) = (s x)).
Proof. exact (@lem8126511 A (term142 A C P s u x) (s x)). Qed.
Lemma lem8126513 {A C P : Type'} (u : C) (s : P -> A) (x : P) : (term142 A C P s u x) = (s x).
Proof. exact (EQ_MP (@lem8126512 A C P u s x) (@lem8126508 A C P u s x)). Qed.
Lemma lem8126514 {A C P : Type'} (u : C) (s : P -> A) (x : P) : (term142 A C P s u x) = (s x).
Proof. exact (@lem8126513 A C P u s x). Qed.
Lemma lem8126515 {A C P : Type'} (p1 : C) (s : P -> A) (p2 : P) : (term142 A C P s p1 p2) = (s p2).
Proof. exact (@lem8126514 A C P p1 s p2). Qed.
Lemma lem8126516 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8126517 {A C P : Type'} (p1 : C) (lt2 : type1402 A) (z : A) (s : P -> A) (p2 : P) : (term143 A C P lt2 z s p1 p2) = (term144 A P lt2 z s p2).
Proof. exact (MK_COMB (@lem8126516 A lt2 z) (@lem8126515 A C P p1 s p2)). Qed.
Lemma lem8126518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8126519 {A C P : Type'} (p1 : C) (lt2 : type1402 A) (z : A) (s : P -> A) (p2 : P) : (term145 A C P lt2 z s p1 p2) = (term146 A P lt2 z s p2).
Proof. exact (MK_COMB (@lem8126518) (@lem8126517 A C P p1 lt2 z s p2)). Qed.
Lemma lem8126524 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((f z) = (g z)).
Proof. exact (eq_refl ((f z) = (g z))). Qed.
Lemma lem8126525 {A B C P : Type'} (p1 : C) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term147 A B C P lt2 s p1 p2 f g z) = (term148 A B P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8126519 A C P p1 lt2 z s p2) (@lem8126524 A B f g z)). Qed.
Lemma lem8126528 {A B C P : Type'} (p1 : C) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term149 A B C P lt2 s p1 p2 f g) = (term150 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8126525 A B C P p1 lt2 s p2 f g z)). Qed.
Lemma lem8126529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8126530 {A B C P : Type'} (p1 : C) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term151 A B C P lt2 s p1 p2 f g) = (term152 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8126529 A) (@lem8126528 A B C P p1 lt2 s p2 f g)). Qed.
Lemma lem8126537 {A B C P : Type'} (p1 : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term153 A B C P p lt2 s p1 p2 f g) = (term154 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8126408 A B C P p1 p g p2) (@lem8126530 A B C P p1 lt2 s p2 f g)). Qed.
Lemma lem8126540 {A B C P : Type'} (p1 : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term155 A B C P p lt2 s p1 p2 f g) = (term156 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8126277 A B C P p1 p f p2) (@lem8126537 A B C P p1 p lt2 s p2 f g)). Qed.
Lemma lem8126543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8126544 {A B C P : Type'} (p1 : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term157 A B C P p lt2 s p1 p2 f g) = (term158 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8126543) (@lem8126540 A B C P p1 p lt2 s p2 f g)). Qed.
Lemma lem8126550 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126551 {A B C P : Type'} (f : type541 A B C P) (y : A -> B) : (term49 A B C P f y) = (f y).
Proof. exact (@lem8126550 (A -> B) (type1210 C P) f y). Qed.
Lemma lem8126552 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term159 A B C P t f) = (term160 A B C P t f).
Proof. exact (@lem8126551 A B C P (term27 A B C P t) f). Qed.
Lemma lem8126553 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term160 A B C P t f) = (term161 A B C P t f).
Proof. exact (eq_refl (term160 A B C P t f)). Qed.
Lemma lem8126554 {A B C P : Type'} (t : type554 A B C P) : (term162 A B C P t) = (term27 A B C P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8126553 A B C P t f)). Qed.
Lemma lem8126555 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8126556 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term159 A B C P t f) = (term160 A B C P t f).
Proof. exact (MK_COMB (@lem8126554 A B C P t) (@lem8126555 A B f)). Qed.
Lemma lem8126557 {C P : Type'} : (@eq ((prod C P) -> Prop)) = (@eq ((prod C P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod C P) -> Prop))). Qed.
Lemma lem8126558 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term163 A B C P t f) = (term164 A B C P t f).
Proof. exact (MK_COMB (@lem8126557 C P) (@lem8126556 A B C P t f)). Qed.
Lemma lem8126559 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term160 A B C P t f) = (term161 A B C P t f).
Proof. exact (eq_refl (term160 A B C P t f)). Qed.
Lemma lem8126560 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : ((term159 A B C P t f) = (term160 A B C P t f)) = ((term160 A B C P t f) = (term161 A B C P t f)).
Proof. exact (MK_COMB (@lem8126558 A B C P t f) (@lem8126559 A B C P t f)). Qed.
Lemma lem8126561 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term160 A B C P t f) = (term161 A B C P t f).
Proof. exact (EQ_MP (@lem8126560 A B C P t f) (@lem8126552 A B C P t f)). Qed.
Lemma lem8126574 {C P : Type'} (p1 : C) (p2 : P) : (@pair C P p1 p2) = (@pair C P p1 p2).
Proof. exact (eq_refl (@pair C P p1 p2)). Qed.
Lemma lem8126575 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term165 A B C P t f p1 p2) = (term166 A B C P t f p1 p2).
Proof. exact (MK_COMB (@lem8126561 A B C P t f) (@lem8126574 C P p1 p2)). Qed.
Lemma lem8126576 {C P : Type'} (a0 : C) (a1 : P) : a0 = (term58 C P a0 a1).
Proof. exact (@lem51128 C P a0 a1). Qed.
Lemma lem8126577 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (@lem8126576 C P u x). Qed.
Lemma lem8126578 {C P : Type'} (a0 : C) (a1 : P) : a1 = (term59 C P a0 a1).
Proof. exact (@lem51159 C P a0 a1). Qed.
Lemma lem8126579 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (@lem8126578 C P u x). Qed.
Lemma lem8126580 {C : Type'} (u : C) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem8126581 {C : Type'} : (term60 C) = (term60 C).
Proof. exact (eq_refl (term60 C)). Qed.
Lemma lem8126582 {C P : Type'} (u : C) (x : P) : (term61 C u) = (term62 C P u x).
Proof. exact (MK_COMB (@lem8126581 C) (@lem8126577 C P u x)). Qed.
Lemma lem8126583 {C P : Type'} (u : C) (x : P) : (term62 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term62 C P u x)). Qed.
Lemma lem8126584 {C : Type'} (u : C) : (term63 C u) = (term63 C u).
Proof. exact (eq_refl (term63 C u)). Qed.
Lemma lem8126585 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = ((term61 C u) = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126584 C u) (@lem8126583 C P u x)). Qed.
Lemma lem8126586 {C : Type'} (u : C) : (term61 C u) = u.
Proof. exact (eq_refl (term61 C u)). Qed.
Lemma lem8126587 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8126588 {C : Type'} (u : C) : (term63 C u) = (@eq C u).
Proof. exact (MK_COMB (@lem8126587 C) (@lem8126586 C u)). Qed.
Lemma lem8126589 {C P : Type'} (u : C) (x : P) : (term58 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term58 C P u x)). Qed.
Lemma lem8126590 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term58 C P u x)) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126588 C u) (@lem8126589 C P u x)). Qed.
Lemma lem8126591 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = (u = (term58 C P u x)).
Proof. exact (TRANS (@lem8126585 C P u x) (@lem8126590 C P u x)). Qed.
Lemma lem8126592 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126591 C P u x) (@lem8126582 C P u x)). Qed.
Lemma lem8126593 {C : Type'} (u : C) : (@eq C u) = (@eq C u).
Proof. exact (eq_refl (@eq C u)). Qed.
Lemma lem8126594 {C P : Type'} (u : C) (x : P) : (u = u) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126593 C u) (@lem8126592 C P u x)). Qed.
Lemma lem8126595 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126594 C P u x) (@lem8126580 C u)). Qed.
Lemma lem8126596 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126597 {P : Type'} : (term60 P) = (term60 P).
Proof. exact (eq_refl (term60 P)). Qed.
Lemma lem8126598 {C P : Type'} (u : C) (x : P) : (term61 P x) = (term64 C P u x).
Proof. exact (MK_COMB (@lem8126597 P) (@lem8126579 C P u x)). Qed.
Lemma lem8126599 {C P : Type'} (u : C) (x : P) : (term64 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term64 C P u x)). Qed.
Lemma lem8126600 {P : Type'} (x : P) : (term63 P x) = (term63 P x).
Proof. exact (eq_refl (term63 P x)). Qed.
Lemma lem8126601 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = ((term61 P x) = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126600 P x) (@lem8126599 C P u x)). Qed.
Lemma lem8126602 {P : Type'} (x : P) : (term61 P x) = x.
Proof. exact (eq_refl (term61 P x)). Qed.
Lemma lem8126603 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8126604 {P : Type'} (x : P) : (term63 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8126603 P) (@lem8126602 P x)). Qed.
Lemma lem8126605 {C P : Type'} (u : C) (x : P) : (term59 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term59 C P u x)). Qed.
Lemma lem8126606 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term59 C P u x)) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126604 P x) (@lem8126605 C P u x)). Qed.
Lemma lem8126607 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = (x = (term59 C P u x)).
Proof. exact (TRANS (@lem8126601 C P u x) (@lem8126606 C P u x)). Qed.
Lemma lem8126608 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126607 C P u x) (@lem8126598 C P u x)). Qed.
Lemma lem8126609 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8126610 {C P : Type'} (u : C) (x : P) : (x = x) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126609 P x) (@lem8126608 C P u x)). Qed.
Lemma lem8126611 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126610 C P u x) (@lem8126596 P x)). Qed.
Lemma lem8126612 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term167 A B C P t f) = (term167 A B C P t f).
Proof. exact (eq_refl (term167 A B C P t f)). Qed.
Lemma lem8126613 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term168 A B C P t f u) = (term169 A B C P t f u x).
Proof. exact (MK_COMB (@lem8126612 A B C P t f) (@lem8126595 C P u x)). Qed.
Lemma lem8126614 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term169 A B C P t f u x) = (term170 A B C P t f u x).
Proof. exact (eq_refl (term169 A B C P t f u x)). Qed.
Lemma lem8126615 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) : (term171 A B C P t f u) = (term171 A B C P t f u).
Proof. exact (eq_refl (term171 A B C P t f u)). Qed.
Lemma lem8126616 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : ((term168 A B C P t f u) = (term169 A B C P t f u x)) = ((term168 A B C P t f u) = (term170 A B C P t f u x)).
Proof. exact (MK_COMB (@lem8126615 A B C P t f u) (@lem8126614 A B C P t f u x)). Qed.
Lemma lem8126617 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) : (term168 A B C P t f u) = (term172 A B C P t f u).
Proof. exact (eq_refl (term168 A B C P t f u)). Qed.
Lemma lem8126618 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8126619 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) : (term171 A B C P t f u) = (term173 A B C P t f u).
Proof. exact (MK_COMB (@lem8126618 P) (@lem8126617 A B C P t f u)). Qed.
Lemma lem8126620 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term170 A B C P t f u x) = (term170 A B C P t f u x).
Proof. exact (eq_refl (term170 A B C P t f u x)). Qed.
Lemma lem8126621 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : ((term168 A B C P t f u) = (term170 A B C P t f u x)) = ((term172 A B C P t f u) = (term170 A B C P t f u x)).
Proof. exact (MK_COMB (@lem8126619 A B C P t f u) (@lem8126620 A B C P t f u x)). Qed.
Lemma lem8126622 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : ((term168 A B C P t f u) = (term169 A B C P t f u x)) = ((term172 A B C P t f u) = (term170 A B C P t f u x)).
Proof. exact (TRANS (@lem8126616 A B C P t f u x) (@lem8126621 A B C P t f u x)). Qed.
Lemma lem8126623 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term172 A B C P t f u) = (term170 A B C P t f u x).
Proof. exact (EQ_MP (@lem8126622 A B C P t f u x) (@lem8126613 A B C P t f u x)). Qed.
Lemma lem8126624 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term174 A B C P t f u x) = (term175 A B C P t f u x).
Proof. exact (MK_COMB (@lem8126623 A B C P t f u x) (@lem8126611 C P u x)). Qed.
Lemma lem8126625 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term175 A B C P t f u x) = (term176 A B C P t f u x).
Proof. exact (eq_refl (term175 A B C P t f u x)). Qed.
Lemma lem8126626 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term177 A B C P t f u x) = (term177 A B C P t f u x).
Proof. exact (eq_refl (term177 A B C P t f u x)). Qed.
Lemma lem8126627 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : ((term174 A B C P t f u x) = (term175 A B C P t f u x)) = ((term174 A B C P t f u x) = (term176 A B C P t f u x)).
Proof. exact (MK_COMB (@lem8126626 A B C P t f u x) (@lem8126625 A B C P t f u x)). Qed.
Lemma lem8126628 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term174 A B C P t f u x) = (t f u x).
Proof. exact (eq_refl (term174 A B C P t f u x)). Qed.
Lemma lem8126629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126630 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term177 A B C P t f u x) = (term178 A B C P t f u x).
Proof. exact (MK_COMB (@lem8126629) (@lem8126628 A B C P t f u x)). Qed.
Lemma lem8126631 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term176 A B C P t f u x) = (term176 A B C P t f u x).
Proof. exact (eq_refl (term176 A B C P t f u x)). Qed.
Lemma lem8126632 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : ((term174 A B C P t f u x) = (term176 A B C P t f u x)) = ((t f u x) = (term176 A B C P t f u x)).
Proof. exact (MK_COMB (@lem8126630 A B C P t f u x) (@lem8126631 A B C P t f u x)). Qed.
Lemma lem8126633 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : ((term174 A B C P t f u x) = (term175 A B C P t f u x)) = ((t f u x) = (term176 A B C P t f u x)).
Proof. exact (TRANS (@lem8126627 A B C P t f u x) (@lem8126632 A B C P t f u x)). Qed.
Lemma lem8126634 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (t f u x) = (term176 A B C P t f u x).
Proof. exact (EQ_MP (@lem8126633 A B C P t f u x) (@lem8126624 A B C P t f u x)). Qed.
Lemma lem8126635 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term176 A B C P t f u x) = (t f u x).
Proof. exact (SYM (@lem8126634 A B C P t f u x)). Qed.
Lemma lem8126636 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term179 A B C P t f u x) = (term176 A B C P t f u x).
Proof. exact (eq_refl (term179 A B C P t f u x)). Qed.
Lemma lem8126637 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term179 A B C P t f u x) = (t f u x).
Proof. exact (TRANS (@lem8126636 A B C P t f u x) (@lem8126635 A B C P t f u x)). Qed.
Lemma lem8126638 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) : term180 A B C P t f u.
Proof. exact (fun x : P => @lem8126637 A B C P t f u x). Qed.
Lemma lem8126639 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : term181 A B C P t f.
Proof. exact (fun u : C => @lem8126638 A B C P t f u). Qed.
Lemma lem8126640 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : term182 A B C P t f.
Proof. exact (ex_intro (term183 A B C P t f) (term184 A B C P t f) (@lem8126639 A B C P t f)). Qed.
Lemma lem8126642 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8126643 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8126642 Prop a b). Qed.
Lemma lem8126644 {A B C P : Type'} (_107614 : type1210 C P) (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : ((term82 C P _107614 u x) = (t f u x)) = (term185 A B C P _107614 t f u x).
Proof. exact (@lem8126643 (term82 C P _107614 u x) (t f u x)). Qed.
Lemma lem8126645 {A B C P : Type'} (_107614 : type1210 C P) (t : type554 A B C P) (f : A -> B) (u : C) : (term186 A B C P _107614 t f u) = (term187 A B C P _107614 t f u).
Proof. exact (fun_ext (fun x : P => @lem8126644 A B C P _107614 t f u x)). Qed.
Lemma lem8126646 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8126647 {A B C P : Type'} (_107614 : type1210 C P) (t : type554 A B C P) (f : A -> B) (u : C) : (term188 A B C P _107614 t f u) = (term189 A B C P _107614 t f u).
Proof. exact (MK_COMB (@lem8126646 P) (@lem8126645 A B C P _107614 t f u)). Qed.
Lemma lem8126648 {A B C P : Type'} (_107614 : type1210 C P) (t : type554 A B C P) (f : A -> B) : (term190 A B C P _107614 t f) = (term191 A B C P _107614 t f).
Proof. exact (fun_ext (fun u : C => @lem8126647 A B C P _107614 t f u)). Qed.
Lemma lem8126649 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8126650 {A B C P : Type'} (_107614 : type1210 C P) (t : type554 A B C P) (f : A -> B) : (term192 A B C P _107614 t f) = (term193 A B C P _107614 t f).
Proof. exact (MK_COMB (@lem8126649 C) (@lem8126648 A B C P _107614 t f)). Qed.
Lemma lem8126651 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term183 A B C P t f) = (term194 A B C P t f).
Proof. exact (fun_ext (fun _107614 : type1210 C P => @lem8126650 A B C P _107614 t f)). Qed.
Lemma lem8126652 {C P : Type'} : (@ex ((prod C P) -> Prop)) = (@ex ((prod C P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod C P) -> Prop))). Qed.
Lemma lem8126653 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term182 A B C P t f) = (term195 A B C P t f).
Proof. exact (MK_COMB (@lem8126652 C P) (@lem8126651 A B C P t f)). Qed.
Lemma lem8126654 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : term195 A B C P t f.
Proof. exact (EQ_MP (@lem8126653 A B C P t f) (@lem8126640 A B C P t f)). Qed.
Lemma lem8126656 {_5076 : Type'} (P : _5076 -> Prop) : term94 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8126657 {C P : Type'} (P' : type324 C P) : term95 C P P'.
Proof. exact (@lem8126656 (type1210 C P) P'). Qed.
Lemma lem8126658 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : term196 A B C P t f.
Proof. exact (@lem8126657 C P (term194 A B C P t f)). Qed.
Lemma lem8126659 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : term197 A B C P t f.
Proof. exact (@lem8126658 A B C P t f (@lem8126654 A B C P t f)). Qed.
Lemma lem8126660 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term197 A B C P t f) = (term198 A B C P t f).
Proof. exact (eq_refl (term197 A B C P t f)). Qed.
Lemma lem8126661 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : term198 A B C P t f.
Proof. exact (EQ_MP (@lem8126660 A B C P t f) (@lem8126659 A B C P t f)). Qed.
Lemma lem8126662 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) : term199 A B C P t f u.
Proof. exact (@lem8126661 A B C P t f u). Qed.
Lemma lem8126663 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) : (term199 A B C P t f u) = (term200 A B C P t f u).
Proof. exact (eq_refl (term199 A B C P t f u)). Qed.
Lemma lem8126664 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) : term200 A B C P t f u.
Proof. exact (EQ_MP (@lem8126663 A B C P t f u) (@lem8126662 A B C P t f u)). Qed.
Lemma lem8126665 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : term201 A B C P t f u x.
Proof. exact (@lem8126664 A B C P t f u x). Qed.
Lemma lem8126666 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term201 A B C P t f u x) = (term202 A B C P t f u x).
Proof. exact (eq_refl (term201 A B C P t f u x)). Qed.
Lemma lem8126667 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : term202 A B C P t f u x.
Proof. exact (EQ_MP (@lem8126666 A B C P t f u x) (@lem8126665 A B C P t f u x)). Qed.
Lemma lem8126669 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8126670 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8126669 Prop a b). Qed.
Lemma lem8126671 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term202 A B C P t f u x) = ((term166 A B C P t f u x) = (t f u x)).
Proof. exact (@lem8126670 (term166 A B C P t f u x) (t f u x)). Qed.
Lemma lem8126672 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term166 A B C P t f u x) = (t f u x).
Proof. exact (EQ_MP (@lem8126671 A B C P t f u x) (@lem8126667 A B C P t f u x)). Qed.
Lemma lem8126673 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (x : P) : (term166 A B C P t f u x) = (t f u x).
Proof. exact (@lem8126672 A B C P t f u x). Qed.
Lemma lem8126674 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term166 A B C P t f p1 p2) = (t f p1 p2).
Proof. exact (@lem8126673 A B C P t f p1 p2). Qed.
Lemma lem8126675 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term165 A B C P t f p1 p2) = (t f p1 p2).
Proof. exact (TRANS (@lem8126575 A B C P t f p1 p2) (@lem8126674 A B C P t f p1 p2)). Qed.
Lemma lem8126676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126677 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term203 A B C P t f p1 p2) = (term178 A B C P t f p1 p2).
Proof. exact (MK_COMB (@lem8126676) (@lem8126675 A B C P t f p1 p2)). Qed.
Lemma lem8126679 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126680 {A B C P : Type'} (f : type541 A B C P) (y : A -> B) : (term49 A B C P f y) = (f y).
Proof. exact (@lem8126679 (A -> B) (type1210 C P) f y). Qed.
Lemma lem8126681 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term159 A B C P t g) = (term160 A B C P t g).
Proof. exact (@lem8126680 A B C P (term27 A B C P t) g). Qed.
Lemma lem8126682 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term160 A B C P t f) = (term161 A B C P t f).
Proof. exact (eq_refl (term160 A B C P t f)). Qed.
Lemma lem8126683 {A B C P : Type'} (t : type554 A B C P) : (term162 A B C P t) = (term27 A B C P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8126682 A B C P t f)). Qed.
Lemma lem8126684 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8126685 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term159 A B C P t g) = (term160 A B C P t g).
Proof. exact (MK_COMB (@lem8126683 A B C P t) (@lem8126684 A B g)). Qed.
Lemma lem8126686 {C P : Type'} : (@eq ((prod C P) -> Prop)) = (@eq ((prod C P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod C P) -> Prop))). Qed.
Lemma lem8126687 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term163 A B C P t g) = (term164 A B C P t g).
Proof. exact (MK_COMB (@lem8126686 C P) (@lem8126685 A B C P t g)). Qed.
Lemma lem8126688 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term160 A B C P t g) = (term161 A B C P t g).
Proof. exact (eq_refl (term160 A B C P t g)). Qed.
Lemma lem8126689 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : ((term159 A B C P t g) = (term160 A B C P t g)) = ((term160 A B C P t g) = (term161 A B C P t g)).
Proof. exact (MK_COMB (@lem8126687 A B C P t g) (@lem8126688 A B C P t g)). Qed.
Lemma lem8126690 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term160 A B C P t g) = (term161 A B C P t g).
Proof. exact (EQ_MP (@lem8126689 A B C P t g) (@lem8126681 A B C P t g)). Qed.
Lemma lem8126703 {C P : Type'} (p1 : C) (p2 : P) : (@pair C P p1 p2) = (@pair C P p1 p2).
Proof. exact (eq_refl (@pair C P p1 p2)). Qed.
Lemma lem8126704 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term165 A B C P t g p1 p2) = (term166 A B C P t g p1 p2).
Proof. exact (MK_COMB (@lem8126690 A B C P t g) (@lem8126703 C P p1 p2)). Qed.
Lemma lem8126705 {C P : Type'} (a0 : C) (a1 : P) : a0 = (term58 C P a0 a1).
Proof. exact (@lem51128 C P a0 a1). Qed.
Lemma lem8126706 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (@lem8126705 C P u x). Qed.
Lemma lem8126707 {C P : Type'} (a0 : C) (a1 : P) : a1 = (term59 C P a0 a1).
Proof. exact (@lem51159 C P a0 a1). Qed.
Lemma lem8126708 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (@lem8126707 C P u x). Qed.
Lemma lem8126709 {C : Type'} (u : C) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem8126710 {C : Type'} : (term60 C) = (term60 C).
Proof. exact (eq_refl (term60 C)). Qed.
Lemma lem8126711 {C P : Type'} (u : C) (x : P) : (term61 C u) = (term62 C P u x).
Proof. exact (MK_COMB (@lem8126710 C) (@lem8126706 C P u x)). Qed.
Lemma lem8126712 {C P : Type'} (u : C) (x : P) : (term62 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term62 C P u x)). Qed.
Lemma lem8126713 {C : Type'} (u : C) : (term63 C u) = (term63 C u).
Proof. exact (eq_refl (term63 C u)). Qed.
Lemma lem8126714 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = ((term61 C u) = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126713 C u) (@lem8126712 C P u x)). Qed.
Lemma lem8126715 {C : Type'} (u : C) : (term61 C u) = u.
Proof. exact (eq_refl (term61 C u)). Qed.
Lemma lem8126716 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8126717 {C : Type'} (u : C) : (term63 C u) = (@eq C u).
Proof. exact (MK_COMB (@lem8126716 C) (@lem8126715 C u)). Qed.
Lemma lem8126718 {C P : Type'} (u : C) (x : P) : (term58 C P u x) = (term58 C P u x).
Proof. exact (eq_refl (term58 C P u x)). Qed.
Lemma lem8126719 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term58 C P u x)) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126717 C u) (@lem8126718 C P u x)). Qed.
Lemma lem8126720 {C P : Type'} (u : C) (x : P) : ((term61 C u) = (term62 C P u x)) = (u = (term58 C P u x)).
Proof. exact (TRANS (@lem8126714 C P u x) (@lem8126719 C P u x)). Qed.
Lemma lem8126721 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126720 C P u x) (@lem8126711 C P u x)). Qed.
Lemma lem8126722 {C : Type'} (u : C) : (@eq C u) = (@eq C u).
Proof. exact (eq_refl (@eq C u)). Qed.
Lemma lem8126723 {C P : Type'} (u : C) (x : P) : (u = u) = (u = (term58 C P u x)).
Proof. exact (MK_COMB (@lem8126722 C u) (@lem8126721 C P u x)). Qed.
Lemma lem8126724 {C P : Type'} (u : C) (x : P) : u = (term58 C P u x).
Proof. exact (EQ_MP (@lem8126723 C P u x) (@lem8126709 C u)). Qed.
Lemma lem8126725 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126726 {P : Type'} : (term60 P) = (term60 P).
Proof. exact (eq_refl (term60 P)). Qed.
Lemma lem8126727 {C P : Type'} (u : C) (x : P) : (term61 P x) = (term64 C P u x).
Proof. exact (MK_COMB (@lem8126726 P) (@lem8126708 C P u x)). Qed.
Lemma lem8126728 {C P : Type'} (u : C) (x : P) : (term64 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term64 C P u x)). Qed.
Lemma lem8126729 {P : Type'} (x : P) : (term63 P x) = (term63 P x).
Proof. exact (eq_refl (term63 P x)). Qed.
Lemma lem8126730 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = ((term61 P x) = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126729 P x) (@lem8126728 C P u x)). Qed.
Lemma lem8126731 {P : Type'} (x : P) : (term61 P x) = x.
Proof. exact (eq_refl (term61 P x)). Qed.
Lemma lem8126732 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8126733 {P : Type'} (x : P) : (term63 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8126732 P) (@lem8126731 P x)). Qed.
Lemma lem8126734 {C P : Type'} (u : C) (x : P) : (term59 C P u x) = (term59 C P u x).
Proof. exact (eq_refl (term59 C P u x)). Qed.
Lemma lem8126735 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term59 C P u x)) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126733 P x) (@lem8126734 C P u x)). Qed.
Lemma lem8126736 {C P : Type'} (u : C) (x : P) : ((term61 P x) = (term64 C P u x)) = (x = (term59 C P u x)).
Proof. exact (TRANS (@lem8126730 C P u x) (@lem8126735 C P u x)). Qed.
Lemma lem8126737 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126736 C P u x) (@lem8126727 C P u x)). Qed.
Lemma lem8126738 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8126739 {C P : Type'} (u : C) (x : P) : (x = x) = (x = (term59 C P u x)).
Proof. exact (MK_COMB (@lem8126738 P x) (@lem8126737 C P u x)). Qed.
Lemma lem8126740 {C P : Type'} (u : C) (x : P) : x = (term59 C P u x).
Proof. exact (EQ_MP (@lem8126739 C P u x) (@lem8126725 P x)). Qed.
Lemma lem8126741 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term167 A B C P t g) = (term167 A B C P t g).
Proof. exact (eq_refl (term167 A B C P t g)). Qed.
Lemma lem8126742 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term168 A B C P t g u) = (term169 A B C P t g u x).
Proof. exact (MK_COMB (@lem8126741 A B C P t g) (@lem8126724 C P u x)). Qed.
Lemma lem8126743 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term169 A B C P t g u x) = (term170 A B C P t g u x).
Proof. exact (eq_refl (term169 A B C P t g u x)). Qed.
Lemma lem8126744 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) : (term171 A B C P t g u) = (term171 A B C P t g u).
Proof. exact (eq_refl (term171 A B C P t g u)). Qed.
Lemma lem8126745 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : ((term168 A B C P t g u) = (term169 A B C P t g u x)) = ((term168 A B C P t g u) = (term170 A B C P t g u x)).
Proof. exact (MK_COMB (@lem8126744 A B C P t g u) (@lem8126743 A B C P t g u x)). Qed.
Lemma lem8126746 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) : (term168 A B C P t g u) = (term172 A B C P t g u).
Proof. exact (eq_refl (term168 A B C P t g u)). Qed.
Lemma lem8126747 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8126748 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) : (term171 A B C P t g u) = (term173 A B C P t g u).
Proof. exact (MK_COMB (@lem8126747 P) (@lem8126746 A B C P t g u)). Qed.
Lemma lem8126749 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term170 A B C P t g u x) = (term170 A B C P t g u x).
Proof. exact (eq_refl (term170 A B C P t g u x)). Qed.
Lemma lem8126750 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : ((term168 A B C P t g u) = (term170 A B C P t g u x)) = ((term172 A B C P t g u) = (term170 A B C P t g u x)).
Proof. exact (MK_COMB (@lem8126748 A B C P t g u) (@lem8126749 A B C P t g u x)). Qed.
Lemma lem8126751 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : ((term168 A B C P t g u) = (term169 A B C P t g u x)) = ((term172 A B C P t g u) = (term170 A B C P t g u x)).
Proof. exact (TRANS (@lem8126745 A B C P t g u x) (@lem8126750 A B C P t g u x)). Qed.
Lemma lem8126752 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term172 A B C P t g u) = (term170 A B C P t g u x).
Proof. exact (EQ_MP (@lem8126751 A B C P t g u x) (@lem8126742 A B C P t g u x)). Qed.
Lemma lem8126753 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term174 A B C P t g u x) = (term175 A B C P t g u x).
Proof. exact (MK_COMB (@lem8126752 A B C P t g u x) (@lem8126740 C P u x)). Qed.
Lemma lem8126754 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term175 A B C P t g u x) = (term176 A B C P t g u x).
Proof. exact (eq_refl (term175 A B C P t g u x)). Qed.
Lemma lem8126755 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term177 A B C P t g u x) = (term177 A B C P t g u x).
Proof. exact (eq_refl (term177 A B C P t g u x)). Qed.
Lemma lem8126756 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : ((term174 A B C P t g u x) = (term175 A B C P t g u x)) = ((term174 A B C P t g u x) = (term176 A B C P t g u x)).
Proof. exact (MK_COMB (@lem8126755 A B C P t g u x) (@lem8126754 A B C P t g u x)). Qed.
Lemma lem8126757 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term174 A B C P t g u x) = (t g u x).
Proof. exact (eq_refl (term174 A B C P t g u x)). Qed.
Lemma lem8126758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126759 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term177 A B C P t g u x) = (term178 A B C P t g u x).
Proof. exact (MK_COMB (@lem8126758) (@lem8126757 A B C P t g u x)). Qed.
Lemma lem8126760 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term176 A B C P t g u x) = (term176 A B C P t g u x).
Proof. exact (eq_refl (term176 A B C P t g u x)). Qed.
Lemma lem8126761 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : ((term174 A B C P t g u x) = (term176 A B C P t g u x)) = ((t g u x) = (term176 A B C P t g u x)).
Proof. exact (MK_COMB (@lem8126759 A B C P t g u x) (@lem8126760 A B C P t g u x)). Qed.
Lemma lem8126762 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : ((term174 A B C P t g u x) = (term175 A B C P t g u x)) = ((t g u x) = (term176 A B C P t g u x)).
Proof. exact (TRANS (@lem8126756 A B C P t g u x) (@lem8126761 A B C P t g u x)). Qed.
Lemma lem8126763 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (t g u x) = (term176 A B C P t g u x).
Proof. exact (EQ_MP (@lem8126762 A B C P t g u x) (@lem8126753 A B C P t g u x)). Qed.
Lemma lem8126764 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term176 A B C P t g u x) = (t g u x).
Proof. exact (SYM (@lem8126763 A B C P t g u x)). Qed.
Lemma lem8126765 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term179 A B C P t g u x) = (term176 A B C P t g u x).
Proof. exact (eq_refl (term179 A B C P t g u x)). Qed.
Lemma lem8126766 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term179 A B C P t g u x) = (t g u x).
Proof. exact (TRANS (@lem8126765 A B C P t g u x) (@lem8126764 A B C P t g u x)). Qed.
Lemma lem8126767 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) : term180 A B C P t g u.
Proof. exact (fun x : P => @lem8126766 A B C P t g u x). Qed.
Lemma lem8126768 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : term181 A B C P t g.
Proof. exact (fun u : C => @lem8126767 A B C P t g u). Qed.
Lemma lem8126769 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : term182 A B C P t g.
Proof. exact (ex_intro (term183 A B C P t g) (term184 A B C P t g) (@lem8126768 A B C P t g)). Qed.
Lemma lem8126771 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8126772 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8126771 Prop a b). Qed.
Lemma lem8126773 {A B C P : Type'} (_107626 : type1210 C P) (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : ((term82 C P _107626 u x) = (t g u x)) = (term185 A B C P _107626 t g u x).
Proof. exact (@lem8126772 (term82 C P _107626 u x) (t g u x)). Qed.
Lemma lem8126774 {A B C P : Type'} (_107626 : type1210 C P) (t : type554 A B C P) (g : A -> B) (u : C) : (term186 A B C P _107626 t g u) = (term187 A B C P _107626 t g u).
Proof. exact (fun_ext (fun x : P => @lem8126773 A B C P _107626 t g u x)). Qed.
Lemma lem8126775 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8126776 {A B C P : Type'} (_107626 : type1210 C P) (t : type554 A B C P) (g : A -> B) (u : C) : (term188 A B C P _107626 t g u) = (term189 A B C P _107626 t g u).
Proof. exact (MK_COMB (@lem8126775 P) (@lem8126774 A B C P _107626 t g u)). Qed.
Lemma lem8126777 {A B C P : Type'} (_107626 : type1210 C P) (t : type554 A B C P) (g : A -> B) : (term190 A B C P _107626 t g) = (term191 A B C P _107626 t g).
Proof. exact (fun_ext (fun u : C => @lem8126776 A B C P _107626 t g u)). Qed.
Lemma lem8126778 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8126779 {A B C P : Type'} (_107626 : type1210 C P) (t : type554 A B C P) (g : A -> B) : (term192 A B C P _107626 t g) = (term193 A B C P _107626 t g).
Proof. exact (MK_COMB (@lem8126778 C) (@lem8126777 A B C P _107626 t g)). Qed.
Lemma lem8126780 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term183 A B C P t g) = (term194 A B C P t g).
Proof. exact (fun_ext (fun _107626 : type1210 C P => @lem8126779 A B C P _107626 t g)). Qed.
Lemma lem8126781 {C P : Type'} : (@ex ((prod C P) -> Prop)) = (@ex ((prod C P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod C P) -> Prop))). Qed.
Lemma lem8126782 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term182 A B C P t g) = (term195 A B C P t g).
Proof. exact (MK_COMB (@lem8126781 C P) (@lem8126780 A B C P t g)). Qed.
Lemma lem8126783 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : term195 A B C P t g.
Proof. exact (EQ_MP (@lem8126782 A B C P t g) (@lem8126769 A B C P t g)). Qed.
Lemma lem8126785 {_5076 : Type'} (P : _5076 -> Prop) : term94 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8126786 {C P : Type'} (P' : type324 C P) : term95 C P P'.
Proof. exact (@lem8126785 (type1210 C P) P'). Qed.
Lemma lem8126787 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : term196 A B C P t g.
Proof. exact (@lem8126786 C P (term194 A B C P t g)). Qed.
Lemma lem8126788 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : term197 A B C P t g.
Proof. exact (@lem8126787 A B C P t g (@lem8126783 A B C P t g)). Qed.
Lemma lem8126789 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term197 A B C P t g) = (term198 A B C P t g).
Proof. exact (eq_refl (term197 A B C P t g)). Qed.
Lemma lem8126790 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : term198 A B C P t g.
Proof. exact (EQ_MP (@lem8126789 A B C P t g) (@lem8126788 A B C P t g)). Qed.
Lemma lem8126791 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) : term199 A B C P t g u.
Proof. exact (@lem8126790 A B C P t g u). Qed.
Lemma lem8126792 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) : (term199 A B C P t g u) = (term200 A B C P t g u).
Proof. exact (eq_refl (term199 A B C P t g u)). Qed.
Lemma lem8126793 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) : term200 A B C P t g u.
Proof. exact (EQ_MP (@lem8126792 A B C P t g u) (@lem8126791 A B C P t g u)). Qed.
Lemma lem8126794 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : term201 A B C P t g u x.
Proof. exact (@lem8126793 A B C P t g u x). Qed.
Lemma lem8126795 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term201 A B C P t g u x) = (term202 A B C P t g u x).
Proof. exact (eq_refl (term201 A B C P t g u x)). Qed.
Lemma lem8126796 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : term202 A B C P t g u x.
Proof. exact (EQ_MP (@lem8126795 A B C P t g u x) (@lem8126794 A B C P t g u x)). Qed.
Lemma lem8126798 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8126799 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8126798 Prop a b). Qed.
Lemma lem8126800 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term202 A B C P t g u x) = ((term166 A B C P t g u x) = (t g u x)).
Proof. exact (@lem8126799 (term166 A B C P t g u x) (t g u x)). Qed.
Lemma lem8126801 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term166 A B C P t g u x) = (t g u x).
Proof. exact (EQ_MP (@lem8126800 A B C P t g u x) (@lem8126796 A B C P t g u x)). Qed.
Lemma lem8126802 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (x : P) : (term166 A B C P t g u x) = (t g u x).
Proof. exact (@lem8126801 A B C P t g u x). Qed.
Lemma lem8126803 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term166 A B C P t g p1 p2) = (t g p1 p2).
Proof. exact (@lem8126802 A B C P t g p1 p2). Qed.
Lemma lem8126804 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term165 A B C P t g p1 p2) = (t g p1 p2).
Proof. exact (TRANS (@lem8126704 A B C P t g p1 p2) (@lem8126803 A B C P t g p1 p2)). Qed.
Lemma lem8126805 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : ((term165 A B C P t f p1 p2) = (term165 A B C P t g p1 p2)) = ((t f p1 p2) = (t g p1 p2)).
Proof. exact (MK_COMB (@lem8126677 A B C P t f p1 p2) (@lem8126804 A B C P t g p1 p2)). Qed.
Lemma lem8126810 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term40 A B C P p lt2 s f t g p1 p2) = (term204 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8126544 A B C P p1 p lt2 s p2 f g) (@lem8126805 A B C P f t g p1 p2)). Qed.
Lemma lem8126813 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term42 A B C P p lt2 s f t g p1) = (term205 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8126810 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8126814 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8126815 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term44 A B C P p lt2 s f t g p1) = (term206 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8126814 P) (@lem8126813 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8126822 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term46 A B C P p lt2 s f t g) = (term207 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8126815 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8126823 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8126824 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term47 A B C P p lt2 s f t g) = (term208 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8126823 C) (@lem8126822 A B C P p lt2 s f t g)). Qed.
Lemma lem8126831 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term36 A B C P p lt2 s f t g) = (term208 A B C P p lt2 s f t g).
Proof. exact (TRANS (@lem8126132 A B C P p lt2 s f t g) (@lem8126824 A B C P p lt2 s f t g)). Qed.
Lemma lem8126832 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term209 A B C P p lt2 s f t) = (term210 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8126831 A B C P p lt2 s f t g)). Qed.
Lemma lem8126833 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8126834 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term211 A B C P p lt2 s f t) = (term212 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8126833 A B) (@lem8126832 A B C P p lt2 s f t)). Qed.
Lemma lem8126841 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term213 A B C P p lt2 s t) = (term214 A B C P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8126834 A B C P p lt2 s f t)). Qed.
Lemma lem8126842 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8126843 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term24 A B C P p lt2 s t) = (term215 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8126842 A B) (@lem8126841 A B C P p lt2 s t)). Qed.
Lemma lem8126850 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term23 A B C P lt2 p s t) = (term215 A B C P p lt2 s t).
Proof. exact (TRANS (@lem8126097 A B C P p lt2 s t) (@lem8126843 A B C P p lt2 s t)). Qed.
Lemma lem8126851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8126852 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term216 A B C P lt2 p s t) = (term217 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8126851) (@lem8126850 A B C P p lt2 s t)). Qed.
Lemma lem8126854 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term21 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8126066 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8126065 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8126855 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type563 A B C P) : (@admissible A B A (C -> Prop) P lt2 p s t) = (term218 A B C P p lt2 s t).
Proof. exact (@lem8126854 A B A (C -> Prop) P p lt2 s t). Qed.
Lemma lem8126856 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term219 A B C P lt2 p s t) = (term220 A B C P p lt2 s t).
Proof. exact (@lem8126855 A B C P p lt2 s (term221 A B C P t)). Qed.
Lemma lem8126896 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term13 A B f g).
Proof. exact (EQ_MP (@lem8126054 A B f g) (@lem8126053 A B f g)). Qed.
Lemma lem8126897 {C : Type'} (f : C -> Prop) (g : C -> Prop) : (f = g) = (term222 C f g).
Proof. exact (@lem8126896 C Prop f g). Qed.
Lemma lem8126898 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : ((term223 A B C P t f a) = (term223 A B C P t g a)) = (term224 A B C P f t g a).
Proof. exact (@lem8126897 C (term223 A B C P t f a) (term223 A B C P t g a)). Qed.
Lemma lem8126910 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126911 {A B C P : Type'} (f : type563 A B C P) (y : A -> B) : (term225 A B C P f y) = (f y).
Proof. exact (@lem8126910 (A -> B) (type1470 C P) f y). Qed.
Lemma lem8126912 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term226 A B C P t f) = (term227 A B C P t f).
Proof. exact (@lem8126911 A B C P (term221 A B C P t) f). Qed.
Lemma lem8126913 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term227 A B C P t f) = (term228 A B C P t f).
Proof. exact (eq_refl (term227 A B C P t f)). Qed.
Lemma lem8126914 {A B C P : Type'} (t : type554 A B C P) : (term229 A B C P t) = (term221 A B C P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8126913 A B C P t f)). Qed.
Lemma lem8126915 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8126916 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term226 A B C P t f) = (term227 A B C P t f).
Proof. exact (MK_COMB (@lem8126914 A B C P t) (@lem8126915 A B f)). Qed.
Lemma lem8126917 {C P : Type'} : (@eq (P -> C -> Prop)) = (@eq (P -> C -> Prop)).
Proof. exact (eq_refl (@eq (P -> C -> Prop))). Qed.
Lemma lem8126918 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term230 A B C P t f) = (term231 A B C P t f).
Proof. exact (MK_COMB (@lem8126917 C P) (@lem8126916 A B C P t f)). Qed.
Lemma lem8126919 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term227 A B C P t f) = (term228 A B C P t f).
Proof. exact (eq_refl (term227 A B C P t f)). Qed.
Lemma lem8126920 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : ((term226 A B C P t f) = (term227 A B C P t f)) = ((term227 A B C P t f) = (term228 A B C P t f)).
Proof. exact (MK_COMB (@lem8126918 A B C P t f) (@lem8126919 A B C P t f)). Qed.
Lemma lem8126921 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term227 A B C P t f) = (term228 A B C P t f).
Proof. exact (EQ_MP (@lem8126920 A B C P t f) (@lem8126912 A B C P t f)). Qed.
Lemma lem8126922 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8126923 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term223 A B C P t f a) = (term232 A B C P t f a).
Proof. exact (MK_COMB (@lem8126921 A B C P t f) (@lem8126922 P a)). Qed.
Lemma lem8126925 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126926 {C P : Type'} (f : type1470 C P) (y : P) : (term233 C P f y) = (f y).
Proof. exact (@lem8126925 P (C -> Prop) f y). Qed.
Lemma lem8126927 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term234 A B C P t f a) = (term232 A B C P t f a).
Proof. exact (@lem8126926 C P (term228 A B C P t f) a). Qed.
Lemma lem8126928 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : P) : (term232 A B C P t f x) = (term235 A B C P t f x).
Proof. exact (eq_refl (term232 A B C P t f x)). Qed.
Lemma lem8126929 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term236 A B C P t f) = (term228 A B C P t f).
Proof. exact (fun_ext (fun x : P => @lem8126928 A B C P t f x)). Qed.
Lemma lem8126930 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8126931 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term234 A B C P t f a) = (term232 A B C P t f a).
Proof. exact (MK_COMB (@lem8126929 A B C P t f) (@lem8126930 P a)). Qed.
Lemma lem8126932 {C : Type'} : (@eq (C -> Prop)) = (@eq (C -> Prop)).
Proof. exact (eq_refl (@eq (C -> Prop))). Qed.
Lemma lem8126933 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term237 A B C P t f a) = (term238 A B C P t f a).
Proof. exact (MK_COMB (@lem8126932 C) (@lem8126931 A B C P t f a)). Qed.
Lemma lem8126934 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term232 A B C P t f a) = (term235 A B C P t f a).
Proof. exact (eq_refl (term232 A B C P t f a)). Qed.
Lemma lem8126935 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : ((term234 A B C P t f a) = (term232 A B C P t f a)) = ((term232 A B C P t f a) = (term235 A B C P t f a)).
Proof. exact (MK_COMB (@lem8126933 A B C P t f a) (@lem8126934 A B C P t f a)). Qed.
Lemma lem8126936 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term232 A B C P t f a) = (term235 A B C P t f a).
Proof. exact (EQ_MP (@lem8126935 A B C P t f a) (@lem8126927 A B C P t f a)). Qed.
Lemma lem8126937 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term223 A B C P t f a) = (term235 A B C P t f a).
Proof. exact (TRANS (@lem8126923 A B C P t f a) (@lem8126936 A B C P t f a)). Qed.
Lemma lem8126938 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126939 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) (x : C) : (term239 A B C P t f a x) = (term240 A B C P t f a x).
Proof. exact (MK_COMB (@lem8126937 A B C P t f a) (@lem8126938 C x)). Qed.
Lemma lem8126941 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126942 {C : Type'} (f : C -> Prop) (y : C) : (term241 C f y) = (f y).
Proof. exact (@lem8126941 C Prop f y). Qed.
Lemma lem8126943 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) (x : C) : (term242 A B C P t f a x) = (term240 A B C P t f a x).
Proof. exact (@lem8126942 C (term235 A B C P t f a) x). Qed.
Lemma lem8126944 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (u : C) (a : P) : (term240 A B C P t f a u) = (t f u a).
Proof. exact (eq_refl (term240 A B C P t f a u)). Qed.
Lemma lem8126945 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) : (term243 A B C P t f a) = (term235 A B C P t f a).
Proof. exact (fun_ext (fun u : C => @lem8126944 A B C P t f u a)). Qed.
Lemma lem8126946 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126947 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) (x : C) : (term242 A B C P t f a x) = (term240 A B C P t f a x).
Proof. exact (MK_COMB (@lem8126945 A B C P t f a) (@lem8126946 C x)). Qed.
Lemma lem8126948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126949 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (a : P) (x : C) : (term244 A B C P t f a x) = (term245 A B C P t f a x).
Proof. exact (MK_COMB (@lem8126948) (@lem8126947 A B C P t f a x)). Qed.
Lemma lem8126950 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term240 A B C P t f a x) = (t f x a).
Proof. exact (eq_refl (term240 A B C P t f a x)). Qed.
Lemma lem8126951 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : ((term242 A B C P t f a x) = (term240 A B C P t f a x)) = ((term240 A B C P t f a x) = (t f x a)).
Proof. exact (MK_COMB (@lem8126949 A B C P t f a x) (@lem8126950 A B C P t f x a)). Qed.
Lemma lem8126952 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term240 A B C P t f a x) = (t f x a).
Proof. exact (EQ_MP (@lem8126951 A B C P t f x a) (@lem8126943 A B C P t f a x)). Qed.
Lemma lem8126953 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term239 A B C P t f a x) = (t f x a).
Proof. exact (TRANS (@lem8126939 A B C P t f a x) (@lem8126952 A B C P t f x a)). Qed.
Lemma lem8126954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126955 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term246 A B C P t f a x) = (term178 A B C P t f x a).
Proof. exact (MK_COMB (@lem8126954) (@lem8126953 A B C P t f x a)). Qed.
Lemma lem8126957 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126958 {A B C P : Type'} (f : type563 A B C P) (y : A -> B) : (term225 A B C P f y) = (f y).
Proof. exact (@lem8126957 (A -> B) (type1470 C P) f y). Qed.
Lemma lem8126959 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term226 A B C P t g) = (term227 A B C P t g).
Proof. exact (@lem8126958 A B C P (term221 A B C P t) g). Qed.
Lemma lem8126960 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (term227 A B C P t f) = (term228 A B C P t f).
Proof. exact (eq_refl (term227 A B C P t f)). Qed.
Lemma lem8126961 {A B C P : Type'} (t : type554 A B C P) : (term229 A B C P t) = (term221 A B C P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8126960 A B C P t f)). Qed.
Lemma lem8126962 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8126963 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term226 A B C P t g) = (term227 A B C P t g).
Proof. exact (MK_COMB (@lem8126961 A B C P t) (@lem8126962 A B g)). Qed.
Lemma lem8126964 {C P : Type'} : (@eq (P -> C -> Prop)) = (@eq (P -> C -> Prop)).
Proof. exact (eq_refl (@eq (P -> C -> Prop))). Qed.
Lemma lem8126965 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term230 A B C P t g) = (term231 A B C P t g).
Proof. exact (MK_COMB (@lem8126964 C P) (@lem8126963 A B C P t g)). Qed.
Lemma lem8126966 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term227 A B C P t g) = (term228 A B C P t g).
Proof. exact (eq_refl (term227 A B C P t g)). Qed.
Lemma lem8126967 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : ((term226 A B C P t g) = (term227 A B C P t g)) = ((term227 A B C P t g) = (term228 A B C P t g)).
Proof. exact (MK_COMB (@lem8126965 A B C P t g) (@lem8126966 A B C P t g)). Qed.
Lemma lem8126968 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term227 A B C P t g) = (term228 A B C P t g).
Proof. exact (EQ_MP (@lem8126967 A B C P t g) (@lem8126959 A B C P t g)). Qed.
Lemma lem8126969 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8126970 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term223 A B C P t g a) = (term232 A B C P t g a).
Proof. exact (MK_COMB (@lem8126968 A B C P t g) (@lem8126969 P a)). Qed.
Lemma lem8126972 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126973 {C P : Type'} (f : type1470 C P) (y : P) : (term233 C P f y) = (f y).
Proof. exact (@lem8126972 P (C -> Prop) f y). Qed.
Lemma lem8126974 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term234 A B C P t g a) = (term232 A B C P t g a).
Proof. exact (@lem8126973 C P (term228 A B C P t g) a). Qed.
Lemma lem8126975 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : P) : (term232 A B C P t g x) = (term235 A B C P t g x).
Proof. exact (eq_refl (term232 A B C P t g x)). Qed.
Lemma lem8126976 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (term236 A B C P t g) = (term228 A B C P t g).
Proof. exact (fun_ext (fun x : P => @lem8126975 A B C P t g x)). Qed.
Lemma lem8126977 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8126978 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term234 A B C P t g a) = (term232 A B C P t g a).
Proof. exact (MK_COMB (@lem8126976 A B C P t g) (@lem8126977 P a)). Qed.
Lemma lem8126979 {C : Type'} : (@eq (C -> Prop)) = (@eq (C -> Prop)).
Proof. exact (eq_refl (@eq (C -> Prop))). Qed.
Lemma lem8126980 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term237 A B C P t g a) = (term238 A B C P t g a).
Proof. exact (MK_COMB (@lem8126979 C) (@lem8126978 A B C P t g a)). Qed.
Lemma lem8126981 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term232 A B C P t g a) = (term235 A B C P t g a).
Proof. exact (eq_refl (term232 A B C P t g a)). Qed.
Lemma lem8126982 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : ((term234 A B C P t g a) = (term232 A B C P t g a)) = ((term232 A B C P t g a) = (term235 A B C P t g a)).
Proof. exact (MK_COMB (@lem8126980 A B C P t g a) (@lem8126981 A B C P t g a)). Qed.
Lemma lem8126983 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term232 A B C P t g a) = (term235 A B C P t g a).
Proof. exact (EQ_MP (@lem8126982 A B C P t g a) (@lem8126974 A B C P t g a)). Qed.
Lemma lem8126984 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term223 A B C P t g a) = (term235 A B C P t g a).
Proof. exact (TRANS (@lem8126970 A B C P t g a) (@lem8126983 A B C P t g a)). Qed.
Lemma lem8126985 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126986 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) (x : C) : (term239 A B C P t g a x) = (term240 A B C P t g a x).
Proof. exact (MK_COMB (@lem8126984 A B C P t g a) (@lem8126985 C x)). Qed.
Lemma lem8126988 {A B : Type'} (f : A -> B) (y : A) : (term48 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8126989 {C : Type'} (f : C -> Prop) (y : C) : (term241 C f y) = (f y).
Proof. exact (@lem8126988 C Prop f y). Qed.
Lemma lem8126990 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) (x : C) : (term242 A B C P t g a x) = (term240 A B C P t g a x).
Proof. exact (@lem8126989 C (term235 A B C P t g a) x). Qed.
Lemma lem8126991 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (u : C) (a : P) : (term240 A B C P t g a u) = (t g u a).
Proof. exact (eq_refl (term240 A B C P t g a u)). Qed.
Lemma lem8126992 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) : (term243 A B C P t g a) = (term235 A B C P t g a).
Proof. exact (fun_ext (fun u : C => @lem8126991 A B C P t g u a)). Qed.
Lemma lem8126993 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8126994 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) (x : C) : (term242 A B C P t g a x) = (term240 A B C P t g a x).
Proof. exact (MK_COMB (@lem8126992 A B C P t g a) (@lem8126993 C x)). Qed.
Lemma lem8126995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8126996 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (a : P) (x : C) : (term244 A B C P t g a x) = (term245 A B C P t g a x).
Proof. exact (MK_COMB (@lem8126995) (@lem8126994 A B C P t g a x)). Qed.
Lemma lem8126997 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term240 A B C P t g a x) = (t g x a).
Proof. exact (eq_refl (term240 A B C P t g a x)). Qed.
Lemma lem8126998 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : ((term242 A B C P t g a x) = (term240 A B C P t g a x)) = ((term240 A B C P t g a x) = (t g x a)).
Proof. exact (MK_COMB (@lem8126996 A B C P t g a x) (@lem8126997 A B C P t g x a)). Qed.
Lemma lem8126999 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term240 A B C P t g a x) = (t g x a).
Proof. exact (EQ_MP (@lem8126998 A B C P t g x a) (@lem8126990 A B C P t g a x)). Qed.
Lemma lem8127000 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term239 A B C P t g a x) = (t g x a).
Proof. exact (TRANS (@lem8126986 A B C P t g a x) (@lem8126999 A B C P t g x a)). Qed.
Lemma lem8127001 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : ((term239 A B C P t f a x) = (term239 A B C P t g a x)) = ((t f x a) = (t g x a)).
Proof. exact (MK_COMB (@lem8126955 A B C P t f x a) (@lem8127000 A B C P t g x a)). Qed.
Lemma lem8127006 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : (term247 A B C P f t g a) = (term248 A B C P f t g a).
Proof. exact (fun_ext (fun x : C => @lem8127001 A B C P f t g x a)). Qed.
Lemma lem8127007 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8127008 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : (term224 A B C P f t g a) = (term249 A B C P f t g a).
Proof. exact (MK_COMB (@lem8127007 C) (@lem8127006 A B C P f t g a)). Qed.
Lemma lem8127015 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : ((term223 A B C P t f a) = (term223 A B C P t g a)) = (term249 A B C P f t g a).
Proof. exact (TRANS (@lem8126898 A B C P f t g a) (@lem8127008 A B C P f t g a)). Qed.
Lemma lem8127016 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term158 A B P p lt2 s a f g) = (term158 A B P p lt2 s a f g).
Proof. exact (eq_refl (term158 A B P p lt2 s a f g)). Qed.
Lemma lem8127017 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : (term250 A B C P p lt2 s f t g a) = (term251 A B C P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8127016 A B P p lt2 s a f g) (@lem8127015 A B C P f t g a)). Qed.
Lemma lem8127020 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term252 A B C P p lt2 s f t g) = (term253 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8127017 A B C P p lt2 s f t g a)). Qed.
Lemma lem8127021 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8127022 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term254 A B C P p lt2 s f t g) = (term255 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127021 P) (@lem8127020 A B C P p lt2 s f t g)). Qed.
Lemma lem8127029 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term256 A B C P p lt2 s f t) = (term257 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8127022 A B C P p lt2 s f t g)). Qed.
Lemma lem8127030 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127031 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term258 A B C P p lt2 s f t) = (term259 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127030 A B) (@lem8127029 A B C P p lt2 s f t)). Qed.
Lemma lem8127038 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term260 A B C P p lt2 s t) = (term261 A B C P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8127031 A B C P p lt2 s f t)). Qed.
Lemma lem8127039 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127040 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term220 A B C P p lt2 s t) = (term262 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127039 A B) (@lem8127038 A B C P p lt2 s t)). Qed.
Lemma lem8127047 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term219 A B C P lt2 p s t) = (term262 A B C P p lt2 s t).
Proof. exact (TRANS (@lem8126856 A B C P p lt2 s t) (@lem8127040 A B C P p lt2 s t)). Qed.
Lemma lem8127048 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term263 A B C P lt2 p s t) = (term264 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8126852 A B C P p lt2 s t) (@lem8127047 A B C P p lt2 s t)). Qed.
Lemma lem8127051 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term265 A B C P lt2 p s) = (term266 A B C P p lt2 s).
Proof. exact (fun_ext (fun t : type554 A B C P => @lem8127048 A B C P p lt2 s t)). Qed.
Lemma lem8127052 {A B C P : Type'} : (@all ((A -> B) -> C -> P -> Prop)) = (@all ((A -> B) -> C -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> C -> P -> Prop))). Qed.
Lemma lem8127053 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term267 A B C P lt2 p s) = (term268 A B C P p lt2 s).
Proof. exact (MK_COMB (@lem8127052 A B C P) (@lem8127051 A B C P p lt2 s)). Qed.
Lemma lem8127060 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term269 A B C P lt2 p) = (term270 A B C P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8127053 A B C P p lt2 s)). Qed.
Lemma lem8127061 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8127062 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term271 A B C P lt2 p) = (term272 A B C P p lt2).
Proof. exact (MK_COMB (@lem8127061 A P) (@lem8127060 A B C P p lt2)). Qed.
Lemma lem8127069 {A B C P : Type'} (lt2 : type1402 A) : (term273 A B C P lt2) = (term274 A B C P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8127062 A B C P p lt2)). Qed.
Lemma lem8127070 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8127071 {A B C P : Type'} (lt2 : type1402 A) : (term275 A B C P lt2) = (term276 A B C P lt2).
Proof. exact (MK_COMB (@lem8127070 A B P) (@lem8127069 A B C P lt2)). Qed.
Lemma lem8127078 {A B C P : Type'} : (term277 A B C P) = (term278 A B C P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8127071 A B C P lt2)). Qed.
Lemma lem8127079 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8127080 {A B C P : Type'} : (term279 A B C P) = (term280 A B C P).
Proof. exact (MK_COMB (@lem8127079 A) (@lem8127078 A B C P)). Qed.
Lemma lem8127087 {A B C P : Type'} : (term280 A B C P) = (term279 A B C P).
Proof. exact (SYM (@lem8127080 A B C P)). Qed.
Lemma lem8127089 (p : Prop) : p = (term281 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8127090 {A B C P : Type'} : (term280 A B C P) = (term282 A B C P).
Proof. exact (@lem8127089 (term280 A B C P)). Qed.
Lemma lem8127091 {A B C P : Type'} : (term282 A B C P) = (term280 A B C P).
Proof. exact (SYM (@lem8127090 A B C P)). Qed.
Lemma lem8127092 {A B C P : Type'} (h1 : term283 A B C P) : term283 A B C P.
Proof. exact (h1). Qed.
Lemma lem8127095 {A B C P : Type'} (h1 : term282 A B C P) : term282 A B C P.
Proof. exact (h1). Qed.
Lemma lem8127096 {A B C P : Type'} : term284 A B C P.
Proof. exact (fun h0 : term282 A B C P => @lem8127095 A B C P h0). Qed.
Lemma lem8127097 {A B C P : Type'} (h1 : term284 A B C P) : term284 A B C P.
Proof. exact (h1). Qed.
Lemma lem8127098 {A B C P : Type'} (h1 : term282 A B C P) : term282 A B C P.
Proof. exact (h1). Qed.
Lemma lem8127099 {A B C P : Type'} (h1 : term282 A B C P) (h2 : term284 A B C P) : term282 A B C P.
Proof. exact (@lem8127097 A B C P h2 (@lem8127098 A B C P h1)). Qed.
Lemma lem8127100 {A B C P : Type'} (h1 : term282 A B C P) : term285 A B C P.
Proof. exact (fun h0 : term284 A B C P => @lem8127099 A B C P h1 h0). Qed.
Lemma lem8127101 {A B C P : Type'} (h1 : term284 A B C P) : term284 A B C P.
Proof. exact (h1). Qed.
Lemma lem8127102 {A B C P : Type'} (h1 : term282 A B C P) (h2 : term284 A B C P) : term282 A B C P.
Proof. exact (@lem8127100 A B C P h1 (@lem8127101 A B C P h2)). Qed.
Lemma lem8127103 {A B C P : Type'} (h1 : term284 A B C P) : term284 A B C P.
Proof. exact (fun h0 : term282 A B C P => @lem8127102 A B C P h0 h1). Qed.
Lemma lem8127104 {A B C P : Type'} : term286 A B C P.
Proof. exact (fun h0 : term284 A B C P => @lem8127103 A B C P h0). Qed.
Lemma lem8127107 {A B C P : Type'} : term284 A B C P.
Proof. exact (@lem8127104 A B C P (@lem8127096 A B C P)). Qed.
Lemma lem8127108 {A B C P : Type'} : term284 A B C P.
Proof. exact (@lem8127107 A B C P). Qed.
Lemma lem8127110 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8127111 {A B C P : Type'} : (term282 A B C P) = (term287 A B C P).
Proof. exact (@lem8127110 (term283 A B C P)). Qed.
Lemma lem8127113 (t : Prop) : (term288 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8127114 {A B C P : Type'} : (term287 A B C P) = (term280 A B C P).
Proof. exact (@lem8127113 (term280 A B C P)). Qed.
Lemma lem8127193 {A B C P : Type'} : (term282 A B C P) = (term280 A B C P).
Proof. exact (TRANS (@lem8127111 A B C P) (@lem8127114 A B C P)). Qed.
Lemma lem8127198 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : ((t f x a) = (t g x a)) = ((t f x a) = (t g x a)).
Proof. exact (eq_refl ((t f x a) = (t g x a))). Qed.
Lemma lem8127199 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : (term248 A B C P f t g a) = (term248 A B C P f t g a).
Proof. exact (fun_ext (fun x : C => @lem8127198 A B C P f t g x a)). Qed.
Lemma lem8127200 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8127201 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : (term249 A B C P f t g a) = (term249 A B C P f t g a).
Proof. exact (MK_COMB (@lem8127200 C) (@lem8127199 A B C P f t g a)). Qed.
Lemma lem8127206 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term148 A B P lt2 s a f g z) = (term148 A B P lt2 s a f g z).
Proof. exact (eq_refl (term148 A B P lt2 s a f g z)). Qed.
Lemma lem8127207 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term150 A B P lt2 s a f g) = (term150 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8127206 A B P lt2 s a f g z)). Qed.
Lemma lem8127208 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8127209 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term152 A B P lt2 s a f g) = (term152 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8127208 A) (@lem8127207 A B P lt2 s a f g)). Qed.
Lemma lem8127212 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term104 A B P p g a) = (term104 A B P p g a).
Proof. exact (eq_refl (term104 A B P p g a)). Qed.
Lemma lem8127213 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term154 A B P p lt2 s a f g) = (term154 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8127212 A B P p g a) (@lem8127209 A B P lt2 s a f g)). Qed.
Lemma lem8127216 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term104 A B P p f a) = (term104 A B P p f a).
Proof. exact (eq_refl (term104 A B P p f a)). Qed.
Lemma lem8127217 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term156 A B P p lt2 s a f g) = (term156 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8127216 A B P p f a) (@lem8127213 A B P p lt2 s a f g)). Qed.
Lemma lem8127218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8127219 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term158 A B P p lt2 s a f g) = (term158 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8127218) (@lem8127217 A B P p lt2 s a f g)). Qed.
Lemma lem8127220 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (a : P) : (term251 A B C P p lt2 s f t g a) = (term251 A B C P p lt2 s f t g a).
Proof. exact (MK_COMB (@lem8127219 A B P p lt2 s a f g) (@lem8127201 A B C P f t g a)). Qed.
Lemma lem8127221 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term253 A B C P p lt2 s f t g) = (term253 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun a : P => @lem8127220 A B C P p lt2 s f t g a)). Qed.
Lemma lem8127222 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8127223 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term255 A B C P p lt2 s f t g) = (term255 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127222 P) (@lem8127221 A B C P p lt2 s f t g)). Qed.
Lemma lem8127224 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term257 A B C P p lt2 s f t) = (term257 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8127223 A B C P p lt2 s f t g)). Qed.
Lemma lem8127225 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127226 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term259 A B C P p lt2 s f t) = (term259 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127225 A B) (@lem8127224 A B C P p lt2 s f t)). Qed.
Lemma lem8127227 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term261 A B C P p lt2 s t) = (term261 A B C P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8127226 A B C P p lt2 s f t)). Qed.
Lemma lem8127228 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127229 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term262 A B C P p lt2 s t) = (term262 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127228 A B) (@lem8127227 A B C P p lt2 s t)). Qed.
Lemma lem8127234 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : ((t f p1 p2) = (t g p1 p2)) = ((t f p1 p2) = (t g p1 p2)).
Proof. exact (eq_refl ((t f p1 p2) = (t g p1 p2))). Qed.
Lemma lem8127239 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term148 A B P lt2 s p2 f g z) = (term148 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term148 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127240 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term150 A B P lt2 s p2 f g) = (term150 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8127239 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127241 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8127242 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term152 A B P lt2 s p2 f g) = (term152 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127241 A) (@lem8127240 A B P lt2 s p2 f g)). Qed.
Lemma lem8127245 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (term104 A B P p g p2) = (term104 A B P p g p2).
Proof. exact (eq_refl (term104 A B P p g p2)). Qed.
Lemma lem8127246 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term154 A B P p lt2 s p2 f g) = (term154 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127245 A B P p g p2) (@lem8127242 A B P lt2 s p2 f g)). Qed.
Lemma lem8127249 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term104 A B P p f p2) = (term104 A B P p f p2).
Proof. exact (eq_refl (term104 A B P p f p2)). Qed.
Lemma lem8127250 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term156 A B P p lt2 s p2 f g) = (term156 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127249 A B P p f p2) (@lem8127246 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8127252 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term158 A B P p lt2 s p2 f g) = (term158 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127251) (@lem8127250 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127253 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term204 A B C P p lt2 s f t g p1 p2) = (term204 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8127252 A B P p lt2 s p2 f g) (@lem8127234 A B C P f t g p1 p2)). Qed.
Lemma lem8127254 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term205 A B C P p lt2 s f t g p1) = (term205 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8127253 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127255 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8127256 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term206 A B C P p lt2 s f t g p1) = (term206 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8127255 P) (@lem8127254 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127257 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term207 A B C P p lt2 s f t g) = (term207 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8127256 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127258 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8127259 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term208 A B C P p lt2 s f t g) = (term208 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127258 C) (@lem8127257 A B C P p lt2 s f t g)). Qed.
Lemma lem8127260 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term210 A B C P p lt2 s f t) = (term210 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8127259 A B C P p lt2 s f t g)). Qed.
Lemma lem8127261 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127262 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term212 A B C P p lt2 s f t) = (term212 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127261 A B) (@lem8127260 A B C P p lt2 s f t)). Qed.
Lemma lem8127263 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term214 A B C P p lt2 s t) = (term214 A B C P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8127262 A B C P p lt2 s f t)). Qed.
Lemma lem8127264 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127265 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term215 A B C P p lt2 s t) = (term215 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127264 A B) (@lem8127263 A B C P p lt2 s t)). Qed.
Lemma lem8127266 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8127267 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term217 A B C P p lt2 s t) = (term217 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127266) (@lem8127265 A B C P p lt2 s t)). Qed.
Lemma lem8127268 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term264 A B C P p lt2 s t) = (term264 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127267 A B C P p lt2 s t) (@lem8127229 A B C P p lt2 s t)). Qed.
Lemma lem8127269 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term266 A B C P p lt2 s) = (term266 A B C P p lt2 s).
Proof. exact (fun_ext (fun t : type554 A B C P => @lem8127268 A B C P p lt2 s t)). Qed.
Lemma lem8127270 {A B C P : Type'} : (@all ((A -> B) -> C -> P -> Prop)) = (@all ((A -> B) -> C -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> C -> P -> Prop))). Qed.
Lemma lem8127271 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term268 A B C P p lt2 s) = (term268 A B C P p lt2 s).
Proof. exact (MK_COMB (@lem8127270 A B C P) (@lem8127269 A B C P p lt2 s)). Qed.
Lemma lem8127272 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term270 A B C P p lt2) = (term270 A B C P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8127271 A B C P p lt2 s)). Qed.
Lemma lem8127273 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8127274 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term272 A B C P p lt2) = (term272 A B C P p lt2).
Proof. exact (MK_COMB (@lem8127273 A P) (@lem8127272 A B C P p lt2)). Qed.
Lemma lem8127275 {A B C P : Type'} (lt2 : type1402 A) : (term274 A B C P lt2) = (term274 A B C P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8127274 A B C P p lt2)). Qed.
Lemma lem8127276 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8127277 {A B C P : Type'} (lt2 : type1402 A) : (term276 A B C P lt2) = (term276 A B C P lt2).
Proof. exact (MK_COMB (@lem8127276 A B P) (@lem8127275 A B C P lt2)). Qed.
Lemma lem8127278 {A B C P : Type'} : (term278 A B C P) = (term278 A B C P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8127277 A B C P lt2)). Qed.
Lemma lem8127279 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8127280 {A B C P : Type'} : (term280 A B C P) = (term280 A B C P).
Proof. exact (MK_COMB (@lem8127279 A) (@lem8127278 A B C P)). Qed.
Lemma lem8127385 {A B C P : Type'} : (term282 A B C P) = (term280 A B C P).
Proof. exact (TRANS (@lem8127193 A B C P) (@lem8127280 A B C P)). Qed.
Lemma lem8127386 {A B C P : Type'} : (term280 A B C P) = (term282 A B C P).
Proof. exact (SYM (@lem8127385 A B C P)). Qed.
Lemma lem8127387 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) (h1 : term215 A B C P p lt2 s t) : term215 A B C P p lt2 s t.
Proof. exact (h1). Qed.
Lemma lem8127388 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term156 A B P p lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8127390 (p : Prop) : p = (term281 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8127391 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : ((t f x a) = (t g x a)) = (term289 A B C P f t g x a).
Proof. exact (@lem8127390 ((t f x a) = (t g x a))). Qed.
Lemma lem8127392 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term289 A B C P f t g x a) = ((t f x a) = (t g x a)).
Proof. exact (SYM (@lem8127391 A B C P f t g x a)). Qed.
Lemma lem8127393 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term290 A B C P f t g x a) : term290 A B C P f t g x a.
Proof. exact (h1). Qed.
Lemma lem8127402 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term291 A B P lt2 s p2 f g z) = (term292 A B P lt2 s p2 f g z).
Proof. exact (@lem17362 (term144 A P lt2 z s p2) ((f z) = (g z))). Qed.
Lemma lem8127403 {A : Type'} (P : A -> Prop) : (term293 A P) = (term294 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem8127404 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term295 A B P lt2 s p2 f g) = (term296 A B P lt2 s p2 f g).
Proof. exact (@lem8127403 A (term150 A B P lt2 s p2 f g)). Qed.
Lemma lem8127405 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term297 A B P lt2 s p2 f g z) = (term148 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term297 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8127407 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term298 A B P lt2 s p2 f g z) = (term291 A B P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8127406) (@lem8127405 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127408 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term298 A B P lt2 s p2 f g z) = (term292 A B P lt2 s p2 f g z).
Proof. exact (TRANS (@lem8127407 A B P lt2 s p2 f g z) (@lem8127402 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127409 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term299 A B P lt2 s p2 f g) = (term300 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8127408 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127410 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127411 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term296 A B P lt2 s p2 f g) = (term301 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127410 A) (@lem8127409 A B P lt2 s p2 f g)). Qed.
Lemma lem8127412 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term295 A B P lt2 s p2 f g) = (term301 A B P lt2 s p2 f g).
Proof. exact (TRANS (@lem8127404 A B P lt2 s p2 f g) (@lem8127411 A B P lt2 s p2 f g)). Qed.
Lemma lem8127414 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (term302 A B P p g p2) = (term302 A B P p g p2).
Proof. exact (eq_refl (term302 A B P p g p2)). Qed.
Lemma lem8127415 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term303 A B P p lt2 s p2 f g) = (term304 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127414 A B P p g p2) (@lem8127412 A B P lt2 s p2 f g)). Qed.
Lemma lem8127416 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term305 A B P p lt2 s p2 f g) = (term303 A B P p lt2 s p2 f g).
Proof. exact (@lem17045 (p g p2) (term152 A B P lt2 s p2 f g)). Qed.
Lemma lem8127417 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term305 A B P p lt2 s p2 f g) = (term304 A B P p lt2 s p2 f g).
Proof. exact (TRANS (@lem8127416 A B P p lt2 s p2 f g) (@lem8127415 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127419 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term302 A B P p f p2) = (term302 A B P p f p2).
Proof. exact (eq_refl (term302 A B P p f p2)). Qed.
Lemma lem8127420 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term306 A B P p lt2 s p2 f g) = (term307 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127419 A B P p f p2) (@lem8127417 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127421 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term308 A B P p lt2 s p2 f g) = (term306 A B P p lt2 s p2 f g).
Proof. exact (@lem17045 (p f p2) (term154 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127422 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term308 A B P p lt2 s p2 f g) = (term307 A B P p lt2 s p2 f g).
Proof. exact (TRANS (@lem8127421 A B P p lt2 s p2 f g) (@lem8127420 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127437 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : ((t f p1 p2) = (t g p1 p2)) = (term309 A B C P f t g p1 p2).
Proof. exact (@lem17784 (t f p1 p2) (t g p1 p2)). Qed.
Lemma lem8127438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8127439 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term310 A B P p lt2 s p2 f g) = (term311 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127438) (@lem8127422 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127440 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term312 A B C P p lt2 s f t g p1 p2) = (term313 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8127439 A B P p lt2 s p2 f g) (@lem8127437 A B C P f t g p1 p2)). Qed.
Lemma lem8127441 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term204 A B C P p lt2 s f t g p1 p2) = (term312 A B C P p lt2 s f t g p1 p2).
Proof. exact (@lem17265 (term156 A B P p lt2 s p2 f g) ((t f p1 p2) = (t g p1 p2))). Qed.
Lemma lem8127442 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term204 A B C P p lt2 s f t g p1 p2) = (term313 A B C P p lt2 s f t g p1 p2).
Proof. exact (TRANS (@lem8127441 A B C P p lt2 s f t g p1 p2) (@lem8127440 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127443 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term205 A B C P p lt2 s f t g p1) = (term314 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8127442 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127444 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8127445 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term206 A B C P p lt2 s f t g p1) = (term315 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8127444 P) (@lem8127443 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127446 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term207 A B C P p lt2 s f t g) = (term316 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8127445 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127447 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8127448 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term208 A B C P p lt2 s f t g) = (term317 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127447 C) (@lem8127446 A B C P p lt2 s f t g)). Qed.
Lemma lem8127449 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term210 A B C P p lt2 s f t) = (term318 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8127448 A B C P p lt2 s f t g)). Qed.
Lemma lem8127450 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127451 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term212 A B C P p lt2 s f t) = (term319 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127450 A B) (@lem8127449 A B C P p lt2 s f t)). Qed.
Lemma lem8127452 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term214 A B C P p lt2 s t) = (term320 A B C P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8127451 A B C P p lt2 s f t)). Qed.
Lemma lem8127453 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127454 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term215 A B C P p lt2 s t) = (term321 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127453 A B) (@lem8127452 A B C P p lt2 s t)). Qed.
Lemma lem8127565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8127566 {A : Type'} (P : Prop) (Q : A -> Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (@lem8127565 A P Q). Qed.
Lemma lem8127567 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term324 A B P p lt2 s p2 f g) = (term325 A B P p lt2 s p2 f g).
Proof. exact (@lem8127566 A (term326 A B P p g p2) (term300 A B P lt2 s p2 f g)). Qed.
Lemma lem8127568 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term327 A B P lt2 s p2 f g z) = (term292 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term327 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127569 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term328 A B P lt2 s p2 f g) = (term300 A B P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8127568 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127570 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127571 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term329 A B P lt2 s p2 f g) = (term301 A B P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127570 A) (@lem8127569 A B P lt2 s p2 f g)). Qed.
Lemma lem8127572 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (term302 A B P p g p2) = (term302 A B P p g p2).
Proof. exact (eq_refl (term302 A B P p g p2)). Qed.
Lemma lem8127573 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term324 A B P p lt2 s p2 f g) = (term304 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127572 A B P p g p2) (@lem8127571 A B P lt2 s p2 f g)). Qed.
Lemma lem8127574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8127575 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term330 A B P p lt2 s p2 f g) = (term331 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127574) (@lem8127573 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127576 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term327 A B P lt2 s p2 f g z) = (term292 A B P lt2 s p2 f g z).
Proof. exact (eq_refl (term327 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127577 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (term302 A B P p g p2) = (term302 A B P p g p2).
Proof. exact (eq_refl (term302 A B P p g p2)). Qed.
Lemma lem8127578 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term332 A B P p lt2 s p2 f g z) = (term333 A B P p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8127577 A B P p g p2) (@lem8127576 A B P lt2 s p2 f g z)). Qed.
Lemma lem8127579 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term334 A B P p lt2 s p2 f g) = (term335 A B P p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8127578 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127580 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127581 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term325 A B P p lt2 s p2 f g) = (term336 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127580 A) (@lem8127579 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127582 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : ((term324 A B P p lt2 s p2 f g) = (term325 A B P p lt2 s p2 f g)) = ((term304 A B P p lt2 s p2 f g) = (term336 A B P p lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8127575 A B P p lt2 s p2 f g) (@lem8127581 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127583 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term304 A B P p lt2 s p2 f g) = (term336 A B P p lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8127582 A B P p lt2 s p2 f g) (@lem8127567 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127584 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term302 A B P p f p2) = (term302 A B P p f p2).
Proof. exact (eq_refl (term302 A B P p f p2)). Qed.
Lemma lem8127585 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term307 A B P p lt2 s p2 f g) = (term337 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127584 A B P p f p2) (@lem8127583 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127587 {A : Type'} (P : Prop) (Q : A -> Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8127588 {A : Type'} (P : Prop) (Q : A -> Prop) : (term322 A P Q) = (term323 A P Q).
Proof. exact (@lem8127587 A P Q). Qed.
Lemma lem8127589 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term338 A B P p lt2 s p2 f g) = (term339 A B P p lt2 s p2 f g).
Proof. exact (@lem8127588 A (term326 A B P p f p2) (term335 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127590 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term340 A B P p lt2 s p2 f g z) = (term333 A B P p lt2 s p2 f g z).
Proof. exact (eq_refl (term340 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127591 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term341 A B P p lt2 s p2 f g) = (term335 A B P p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8127590 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127592 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127593 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term342 A B P p lt2 s p2 f g) = (term336 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127592 A) (@lem8127591 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127594 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term302 A B P p f p2) = (term302 A B P p f p2).
Proof. exact (eq_refl (term302 A B P p f p2)). Qed.
Lemma lem8127595 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term338 A B P p lt2 s p2 f g) = (term337 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127594 A B P p f p2) (@lem8127593 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8127597 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term343 A B P p lt2 s p2 f g) = (term344 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127596) (@lem8127595 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127598 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term340 A B P p lt2 s p2 f g z) = (term333 A B P p lt2 s p2 f g z).
Proof. exact (eq_refl (term340 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127599 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term302 A B P p f p2) = (term302 A B P p f p2).
Proof. exact (eq_refl (term302 A B P p f p2)). Qed.
Lemma lem8127600 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term345 A B P p lt2 s p2 f g z) = (term346 A B P p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8127599 A B P p f p2) (@lem8127598 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127601 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term347 A B P p lt2 s p2 f g) = (term348 A B P p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8127600 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127602 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127603 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term339 A B P p lt2 s p2 f g) = (term349 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127602 A) (@lem8127601 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127604 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : ((term338 A B P p lt2 s p2 f g) = (term339 A B P p lt2 s p2 f g)) = ((term337 A B P p lt2 s p2 f g) = (term349 A B P p lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8127597 A B P p lt2 s p2 f g) (@lem8127603 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127605 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term337 A B P p lt2 s p2 f g) = (term349 A B P p lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8127604 A B P p lt2 s p2 f g) (@lem8127589 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127606 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term307 A B P p lt2 s p2 f g) = (term349 A B P p lt2 s p2 f g).
Proof. exact (TRANS (@lem8127585 A B P p lt2 s p2 f g) (@lem8127605 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8127608 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term311 A B P p lt2 s p2 f g) = (term350 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127607) (@lem8127606 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127609 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term309 A B C P f t g p1 p2) = (term309 A B C P f t g p1 p2).
Proof. exact (eq_refl (term309 A B C P f t g p1 p2)). Qed.
Lemma lem8127610 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term313 A B C P p lt2 s f t g p1 p2) = (term351 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8127608 A B P p lt2 s p2 f g) (@lem8127609 A B C P f t g p1 p2)). Qed.
Lemma lem8127612 {A : Type'} (P : A -> Prop) (Q : Prop) : (term352 A P Q) = (term353 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8127613 {A : Type'} (P : A -> Prop) (Q : Prop) : (term352 A P Q) = (term353 A P Q).
Proof. exact (@lem8127612 A P Q). Qed.
Lemma lem8127614 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term354 A B C P p lt2 s f t g p1 p2) = (term355 A B C P p lt2 s f t g p1 p2).
Proof. exact (@lem8127613 A (term348 A B P p lt2 s p2 f g) (term309 A B C P f t g p1 p2)). Qed.
Lemma lem8127615 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term356 A B P p lt2 s p2 f g z) = (term346 A B P p lt2 s p2 f g z).
Proof. exact (eq_refl (term356 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127616 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term357 A B P p lt2 s p2 f g) = (term348 A B P p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : A => @lem8127615 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127617 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127618 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term358 A B P p lt2 s p2 f g) = (term349 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127617 A) (@lem8127616 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8127620 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) : (term359 A B P p lt2 s p2 f g) = (term350 A B P p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8127619) (@lem8127618 A B P p lt2 s p2 f g)). Qed.
Lemma lem8127621 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term309 A B C P f t g p1 p2) = (term309 A B C P f t g p1 p2).
Proof. exact (eq_refl (term309 A B C P f t g p1 p2)). Qed.
Lemma lem8127622 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term354 A B C P p lt2 s f t g p1 p2) = (term351 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8127620 A B P p lt2 s p2 f g) (@lem8127621 A B C P f t g p1 p2)). Qed.
Lemma lem8127623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8127624 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term360 A B C P p lt2 s f t g p1 p2) = (term361 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8127623) (@lem8127622 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127625 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term356 A B P p lt2 s p2 f g z) = (term346 A B P p lt2 s p2 f g z).
Proof. exact (eq_refl (term356 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8127627 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (p2 : P) (f : A -> B) (g : A -> B) (z : A) : (term362 A B P p lt2 s p2 f g z) = (term363 A B P p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8127626) (@lem8127625 A B P p lt2 s p2 f g z)). Qed.
Lemma lem8127628 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term309 A B C P f t g p1 p2) = (term309 A B C P f t g p1 p2).
Proof. exact (eq_refl (term309 A B C P f t g p1 p2)). Qed.
Lemma lem8127629 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term364 A B C P p lt2 s z f t g p1 p2) = (term365 A B C P p lt2 s z f t g p1 p2).
Proof. exact (MK_COMB (@lem8127627 A B P p lt2 s p2 f g z) (@lem8127628 A B C P f t g p1 p2)). Qed.
Lemma lem8127630 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term366 A B C P p lt2 s f t g p1 p2) = (term367 A B C P p lt2 s f t g p1 p2).
Proof. exact (fun_ext (fun z : A => @lem8127629 A B C P p lt2 s z f t g p1 p2)). Qed.
Lemma lem8127631 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127632 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term355 A B C P p lt2 s f t g p1 p2) = (term368 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8127631 A) (@lem8127630 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127633 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : ((term354 A B C P p lt2 s f t g p1 p2) = (term355 A B C P p lt2 s f t g p1 p2)) = ((term351 A B C P p lt2 s f t g p1 p2) = (term368 A B C P p lt2 s f t g p1 p2)).
Proof. exact (MK_COMB (@lem8127624 A B C P p lt2 s f t g p1 p2) (@lem8127632 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127634 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term351 A B C P p lt2 s f t g p1 p2) = (term368 A B C P p lt2 s f t g p1 p2).
Proof. exact (EQ_MP (@lem8127633 A B C P p lt2 s f t g p1 p2) (@lem8127614 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127635 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term313 A B C P p lt2 s f t g p1 p2) = (term368 A B C P p lt2 s f t g p1 p2).
Proof. exact (TRANS (@lem8127610 A B C P p lt2 s f t g p1 p2) (@lem8127634 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127636 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term314 A B C P p lt2 s f t g p1) = (term369 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8127635 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127637 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8127638 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term315 A B C P p lt2 s f t g p1) = (term370 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8127637 P) (@lem8127636 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127640 {A B : Type'} (P : type1413 A B) : (term371 A B P) = (term372 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8127641 {A P : Type'} (P' : type1470 A P) : (term373 A P P') = (term374 A P P').
Proof. exact (@lem8127640 P A P'). Qed.
Lemma lem8127642 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term375 A B C P p lt2 s f t g p1) = (term376 A B C P p lt2 s f t g p1).
Proof. exact (@lem8127641 A P (term377 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127643 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term378 A B C P p lt2 s f t g p1 p2) = (term367 A B C P p lt2 s f t g p1 p2).
Proof. exact (eq_refl (term378 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127644 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8127645 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) (z : A) : (term379 A B C P p lt2 s f t g p1 p2 z) = (term380 A B C P p lt2 s f t g p1 p2 z).
Proof. exact (MK_COMB (@lem8127643 A B C P p lt2 s f t g p1 p2) (@lem8127644 A z)). Qed.
Lemma lem8127646 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term380 A B C P p lt2 s f t g p1 p2 z) = (term365 A B C P p lt2 s z f t g p1 p2).
Proof. exact (eq_refl (term380 A B C P p lt2 s f t g p1 p2 z)). Qed.
Lemma lem8127647 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term379 A B C P p lt2 s f t g p1 p2 z) = (term365 A B C P p lt2 s z f t g p1 p2).
Proof. exact (TRANS (@lem8127645 A B C P p lt2 s f t g p1 p2 z) (@lem8127646 A B C P p lt2 s z f t g p1 p2)). Qed.
Lemma lem8127648 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term381 A B C P p lt2 s f t g p1 p2) = (term367 A B C P p lt2 s f t g p1 p2).
Proof. exact (fun_ext (fun z : A => @lem8127647 A B C P p lt2 s z f t g p1 p2)). Qed.
Lemma lem8127649 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8127650 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term382 A B C P p lt2 s f t g p1 p2) = (term368 A B C P p lt2 s f t g p1 p2).
Proof. exact (MK_COMB (@lem8127649 A) (@lem8127648 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127651 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term383 A B C P p lt2 s f t g p1) = (term369 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8127650 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127652 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8127653 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term375 A B C P p lt2 s f t g p1) = (term370 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8127652 P) (@lem8127651 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8127655 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term384 A B C P p lt2 s f t g p1) = (term385 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8127654) (@lem8127653 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127656 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term378 A B C P p lt2 s f t g p1 p2) = (term367 A B C P p lt2 s f t g p1 p2).
Proof. exact (eq_refl (term378 A B C P p lt2 s f t g p1 p2)). Qed.
Lemma lem8127657 {A P : Type'} (z : P -> A) (p2 : P) : (z p2) = (z p2).
Proof. exact (eq_refl (z p2)). Qed.
Lemma lem8127658 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (z : P -> A) (p2 : P) : (term386 A B C P p lt2 s f t g p1 z p2) = (term387 A B C P p lt2 s f t g p1 z p2).
Proof. exact (MK_COMB (@lem8127656 A B C P p lt2 s f t g p1 p2) (@lem8127657 A P z p2)). Qed.
Lemma lem8127659 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term387 A B C P p lt2 s f t g p1 z p2) = (term388 A B C P p lt2 s z f t g p1 p2).
Proof. exact (eq_refl (term387 A B C P p lt2 s f t g p1 z p2)). Qed.
Lemma lem8127660 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term386 A B C P p lt2 s f t g p1 z p2) = (term388 A B C P p lt2 s z f t g p1 p2).
Proof. exact (TRANS (@lem8127658 A B C P p lt2 s f t g p1 z p2) (@lem8127659 A B C P p lt2 s z f t g p1 p2)). Qed.
Lemma lem8127661 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term389 A B C P p lt2 s f t g p1 z) = (term390 A B C P p lt2 s z f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8127660 A B C P p lt2 s z f t g p1 p2)). Qed.
Lemma lem8127662 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8127663 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term391 A B C P p lt2 s f t g p1 z) = (term392 A B C P p lt2 s z f t g p1).
Proof. exact (MK_COMB (@lem8127662 P) (@lem8127661 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8127664 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term393 A B C P p lt2 s f t g p1) = (term394 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun z : P -> A => @lem8127663 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8127665 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8127666 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term376 A B C P p lt2 s f t g p1) = (term395 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8127665 A P) (@lem8127664 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127667 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : ((term375 A B C P p lt2 s f t g p1) = (term376 A B C P p lt2 s f t g p1)) = ((term370 A B C P p lt2 s f t g p1) = (term395 A B C P p lt2 s f t g p1)).
Proof. exact (MK_COMB (@lem8127655 A B C P p lt2 s f t g p1) (@lem8127666 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127668 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term370 A B C P p lt2 s f t g p1) = (term395 A B C P p lt2 s f t g p1).
Proof. exact (EQ_MP (@lem8127667 A B C P p lt2 s f t g p1) (@lem8127642 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127669 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term315 A B C P p lt2 s f t g p1) = (term395 A B C P p lt2 s f t g p1).
Proof. exact (TRANS (@lem8127638 A B C P p lt2 s f t g p1) (@lem8127668 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127670 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term316 A B C P p lt2 s f t g) = (term396 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8127669 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127671 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8127672 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term317 A B C P p lt2 s f t g) = (term397 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127671 C) (@lem8127670 A B C P p lt2 s f t g)). Qed.
Lemma lem8127674 {A B : Type'} (P : type1413 A B) : (term371 A B P) = (term372 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8127675 {A C P : Type'} (P' : type1455 A C P) : (term398 A C P P') = (term399 A C P P').
Proof. exact (@lem8127674 C (P -> A) P'). Qed.
Lemma lem8127676 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term400 A B C P p lt2 s f t g) = (term401 A B C P p lt2 s f t g).
Proof. exact (@lem8127675 A C P (term402 A B C P p lt2 s f t g)). Qed.
Lemma lem8127677 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term403 A B C P p lt2 s f t g p1) = (term394 A B C P p lt2 s f t g p1).
Proof. exact (eq_refl (term403 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127678 {A P : Type'} (z : P -> A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8127679 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (z : P -> A) : (term404 A B C P p lt2 s f t g p1 z) = (term405 A B C P p lt2 s f t g p1 z).
Proof. exact (MK_COMB (@lem8127677 A B C P p lt2 s f t g p1) (@lem8127678 A P z)). Qed.
Lemma lem8127680 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term405 A B C P p lt2 s f t g p1 z) = (term392 A B C P p lt2 s z f t g p1).
Proof. exact (eq_refl (term405 A B C P p lt2 s f t g p1 z)). Qed.
Lemma lem8127681 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term404 A B C P p lt2 s f t g p1 z) = (term392 A B C P p lt2 s z f t g p1).
Proof. exact (TRANS (@lem8127679 A B C P p lt2 s f t g p1 z) (@lem8127680 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8127682 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term406 A B C P p lt2 s f t g p1) = (term394 A B C P p lt2 s f t g p1).
Proof. exact (fun_ext (fun z : P -> A => @lem8127681 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8127683 {A P : Type'} : (@ex (P -> A)) = (@ex (P -> A)).
Proof. exact (eq_refl (@ex (P -> A))). Qed.
Lemma lem8127684 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term407 A B C P p lt2 s f t g p1) = (term395 A B C P p lt2 s f t g p1).
Proof. exact (MK_COMB (@lem8127683 A P) (@lem8127682 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127685 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term408 A B C P p lt2 s f t g) = (term396 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8127684 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127686 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8127687 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term400 A B C P p lt2 s f t g) = (term397 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127686 C) (@lem8127685 A B C P p lt2 s f t g)). Qed.
Lemma lem8127688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8127689 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term409 A B C P p lt2 s f t g) = (term410 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127688) (@lem8127687 A B C P p lt2 s f t g)). Qed.
Lemma lem8127690 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term403 A B C P p lt2 s f t g p1) = (term394 A B C P p lt2 s f t g p1).
Proof. exact (eq_refl (term403 A B C P p lt2 s f t g p1)). Qed.
Lemma lem8127691 {A C P : Type'} (z : type1475 A C P) (p1 : C) : (z p1) = (z p1).
Proof. exact (eq_refl (z p1)). Qed.
Lemma lem8127692 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (z : type1475 A C P) (p1 : C) : (term411 A B C P p lt2 s f t g z p1) = (term412 A B C P p lt2 s f t g z p1).
Proof. exact (MK_COMB (@lem8127690 A B C P p lt2 s f t g p1) (@lem8127691 A C P z p1)). Qed.
Lemma lem8127693 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type1475 A C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term412 A B C P p lt2 s f t g z p1) = (term413 A B C P p lt2 s z f t g p1).
Proof. exact (eq_refl (term412 A B C P p lt2 s f t g z p1)). Qed.
Lemma lem8127694 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type1475 A C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term411 A B C P p lt2 s f t g z p1) = (term413 A B C P p lt2 s z f t g p1).
Proof. exact (TRANS (@lem8127692 A B C P p lt2 s f t g z p1) (@lem8127693 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8127695 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type1475 A C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term414 A B C P p lt2 s f t g z) = (term415 A B C P p lt2 s z f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8127694 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8127696 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8127697 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type1475 A C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term416 A B C P p lt2 s f t g z) = (term417 A B C P p lt2 s z f t g).
Proof. exact (MK_COMB (@lem8127696 C) (@lem8127695 A B C P p lt2 s z f t g)). Qed.
Lemma lem8127698 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term418 A B C P p lt2 s f t g) = (term419 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun z : type1475 A C P => @lem8127697 A B C P p lt2 s z f t g)). Qed.
Lemma lem8127699 {A C P : Type'} : (@ex (C -> P -> A)) = (@ex (C -> P -> A)).
Proof. exact (eq_refl (@ex (C -> P -> A))). Qed.
Lemma lem8127700 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term401 A B C P p lt2 s f t g) = (term420 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127699 A C P) (@lem8127698 A B C P p lt2 s f t g)). Qed.
Lemma lem8127701 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : ((term400 A B C P p lt2 s f t g) = (term401 A B C P p lt2 s f t g)) = ((term397 A B C P p lt2 s f t g) = (term420 A B C P p lt2 s f t g)).
Proof. exact (MK_COMB (@lem8127689 A B C P p lt2 s f t g) (@lem8127700 A B C P p lt2 s f t g)). Qed.
Lemma lem8127702 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term397 A B C P p lt2 s f t g) = (term420 A B C P p lt2 s f t g).
Proof. exact (EQ_MP (@lem8127701 A B C P p lt2 s f t g) (@lem8127676 A B C P p lt2 s f t g)). Qed.
Lemma lem8127703 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term317 A B C P p lt2 s f t g) = (term420 A B C P p lt2 s f t g).
Proof. exact (TRANS (@lem8127672 A B C P p lt2 s f t g) (@lem8127702 A B C P p lt2 s f t g)). Qed.
Lemma lem8127704 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term318 A B C P p lt2 s f t) = (term421 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8127703 A B C P p lt2 s f t g)). Qed.
Lemma lem8127705 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127706 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term319 A B C P p lt2 s f t) = (term422 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127705 A B) (@lem8127704 A B C P p lt2 s f t)). Qed.
Lemma lem8127708 {A B : Type'} (P : type1413 A B) : (term371 A B P) = (term372 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8127709 {A B C P : Type'} (P' : type536 A B C P) : (term423 A B C P P') = (term424 A B C P P').
Proof. exact (@lem8127708 (A -> B) (type1475 A C P) P'). Qed.
Lemma lem8127710 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term425 A B C P p lt2 s f t) = (term426 A B C P p lt2 s f t).
Proof. exact (@lem8127709 A B C P (term427 A B C P p lt2 s f t)). Qed.
Lemma lem8127711 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term428 A B C P p lt2 s f t g) = (term419 A B C P p lt2 s f t g).
Proof. exact (eq_refl (term428 A B C P p lt2 s f t g)). Qed.
Lemma lem8127712 {A C P : Type'} (z : type1475 A C P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8127713 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) (z : type1475 A C P) : (term429 A B C P p lt2 s f t g z) = (term430 A B C P p lt2 s f t g z).
Proof. exact (MK_COMB (@lem8127711 A B C P p lt2 s f t g) (@lem8127712 A C P z)). Qed.
Lemma lem8127714 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type1475 A C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term430 A B C P p lt2 s f t g z) = (term417 A B C P p lt2 s z f t g).
Proof. exact (eq_refl (term430 A B C P p lt2 s f t g z)). Qed.
Lemma lem8127715 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type1475 A C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term429 A B C P p lt2 s f t g z) = (term417 A B C P p lt2 s z f t g).
Proof. exact (TRANS (@lem8127713 A B C P p lt2 s f t g z) (@lem8127714 A B C P p lt2 s z f t g)). Qed.
Lemma lem8127716 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term431 A B C P p lt2 s f t g) = (term419 A B C P p lt2 s f t g).
Proof. exact (fun_ext (fun z : type1475 A C P => @lem8127715 A B C P p lt2 s z f t g)). Qed.
Lemma lem8127717 {A C P : Type'} : (@ex (C -> P -> A)) = (@ex (C -> P -> A)).
Proof. exact (eq_refl (@ex (C -> P -> A))). Qed.
Lemma lem8127718 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term432 A B C P p lt2 s f t g) = (term420 A B C P p lt2 s f t g).
Proof. exact (MK_COMB (@lem8127717 A C P) (@lem8127716 A B C P p lt2 s f t g)). Qed.
Lemma lem8127719 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term433 A B C P p lt2 s f t) = (term421 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8127718 A B C P p lt2 s f t g)). Qed.
Lemma lem8127720 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127721 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term425 A B C P p lt2 s f t) = (term422 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127720 A B) (@lem8127719 A B C P p lt2 s f t)). Qed.
Lemma lem8127722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8127723 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term434 A B C P p lt2 s f t) = (term435 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127722) (@lem8127721 A B C P p lt2 s f t)). Qed.
Lemma lem8127724 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term428 A B C P p lt2 s f t g) = (term419 A B C P p lt2 s f t g).
Proof. exact (eq_refl (term428 A B C P p lt2 s f t g)). Qed.
Lemma lem8127725 {A B C P : Type'} (z : type553 A B C P) (g : A -> B) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8127726 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (z : type553 A B C P) (g : A -> B) : (term436 A B C P p lt2 s f t z g) = (term437 A B C P p lt2 s f t z g).
Proof. exact (MK_COMB (@lem8127724 A B C P p lt2 s f t g) (@lem8127725 A B C P z g)). Qed.
Lemma lem8127727 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type553 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term437 A B C P p lt2 s f t z g) = (term438 A B C P p lt2 s z f t g).
Proof. exact (eq_refl (term437 A B C P p lt2 s f t z g)). Qed.
Lemma lem8127728 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type553 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term436 A B C P p lt2 s f t z g) = (term438 A B C P p lt2 s z f t g).
Proof. exact (TRANS (@lem8127726 A B C P p lt2 s f t z g) (@lem8127727 A B C P p lt2 s z f t g)). Qed.
Lemma lem8127729 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type553 A B C P) (f : A -> B) (t : type554 A B C P) : (term439 A B C P p lt2 s f t z) = (term440 A B C P p lt2 s z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8127728 A B C P p lt2 s z f t g)). Qed.
Lemma lem8127730 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127731 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type553 A B C P) (f : A -> B) (t : type554 A B C P) : (term441 A B C P p lt2 s f t z) = (term442 A B C P p lt2 s z f t).
Proof. exact (MK_COMB (@lem8127730 A B) (@lem8127729 A B C P p lt2 s z f t)). Qed.
Lemma lem8127732 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term443 A B C P p lt2 s f t) = (term444 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun z : type553 A B C P => @lem8127731 A B C P p lt2 s z f t)). Qed.
Lemma lem8127733 {A B C P : Type'} : (@ex ((A -> B) -> C -> P -> A)) = (@ex ((A -> B) -> C -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> C -> P -> A))). Qed.
Lemma lem8127734 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term426 A B C P p lt2 s f t) = (term445 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127733 A B C P) (@lem8127732 A B C P p lt2 s f t)). Qed.
Lemma lem8127735 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : ((term425 A B C P p lt2 s f t) = (term426 A B C P p lt2 s f t)) = ((term422 A B C P p lt2 s f t) = (term445 A B C P p lt2 s f t)).
Proof. exact (MK_COMB (@lem8127723 A B C P p lt2 s f t) (@lem8127734 A B C P p lt2 s f t)). Qed.
Lemma lem8127736 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term422 A B C P p lt2 s f t) = (term445 A B C P p lt2 s f t).
Proof. exact (EQ_MP (@lem8127735 A B C P p lt2 s f t) (@lem8127710 A B C P p lt2 s f t)). Qed.
Lemma lem8127737 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term319 A B C P p lt2 s f t) = (term445 A B C P p lt2 s f t).
Proof. exact (TRANS (@lem8127706 A B C P p lt2 s f t) (@lem8127736 A B C P p lt2 s f t)). Qed.
Lemma lem8127738 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term320 A B C P p lt2 s t) = (term446 A B C P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8127737 A B C P p lt2 s f t)). Qed.
Lemma lem8127739 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127740 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term321 A B C P p lt2 s t) = (term447 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127739 A B) (@lem8127738 A B C P p lt2 s t)). Qed.
Lemma lem8127742 {A B : Type'} (P : type1413 A B) : (term371 A B P) = (term372 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8127743 {A B C P : Type'} (P' : type494 A B C P) : (term448 A B C P P') = (term449 A B C P P').
Proof. exact (@lem8127742 (A -> B) (type553 A B C P) P'). Qed.
Lemma lem8127744 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term450 A B C P p lt2 s t) = (term451 A B C P p lt2 s t).
Proof. exact (@lem8127743 A B C P (term452 A B C P p lt2 s t)). Qed.
Lemma lem8127745 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term453 A B C P p lt2 s t f) = (term444 A B C P p lt2 s f t).
Proof. exact (eq_refl (term453 A B C P p lt2 s t f)). Qed.
Lemma lem8127746 {A B C P : Type'} (z : type553 A B C P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8127747 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) (z : type553 A B C P) : (term454 A B C P p lt2 s t f z) = (term455 A B C P p lt2 s f t z).
Proof. exact (MK_COMB (@lem8127745 A B C P p lt2 s f t) (@lem8127746 A B C P z)). Qed.
Lemma lem8127748 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type553 A B C P) (f : A -> B) (t : type554 A B C P) : (term455 A B C P p lt2 s f t z) = (term442 A B C P p lt2 s z f t).
Proof. exact (eq_refl (term455 A B C P p lt2 s f t z)). Qed.
Lemma lem8127749 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type553 A B C P) (f : A -> B) (t : type554 A B C P) : (term454 A B C P p lt2 s t f z) = (term442 A B C P p lt2 s z f t).
Proof. exact (TRANS (@lem8127747 A B C P p lt2 s f t z) (@lem8127748 A B C P p lt2 s z f t)). Qed.
Lemma lem8127750 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term456 A B C P p lt2 s t f) = (term444 A B C P p lt2 s f t).
Proof. exact (fun_ext (fun z : type553 A B C P => @lem8127749 A B C P p lt2 s z f t)). Qed.
Lemma lem8127751 {A B C P : Type'} : (@ex ((A -> B) -> C -> P -> A)) = (@ex ((A -> B) -> C -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> C -> P -> A))). Qed.
Lemma lem8127752 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term457 A B C P p lt2 s t f) = (term445 A B C P p lt2 s f t).
Proof. exact (MK_COMB (@lem8127751 A B C P) (@lem8127750 A B C P p lt2 s f t)). Qed.
Lemma lem8127753 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term458 A B C P p lt2 s t) = (term446 A B C P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8127752 A B C P p lt2 s f t)). Qed.
Lemma lem8127754 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127755 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term450 A B C P p lt2 s t) = (term447 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127754 A B) (@lem8127753 A B C P p lt2 s t)). Qed.
Lemma lem8127756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8127757 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term459 A B C P p lt2 s t) = (term460 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127756) (@lem8127755 A B C P p lt2 s t)). Qed.
Lemma lem8127758 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : type554 A B C P) : (term453 A B C P p lt2 s t f) = (term444 A B C P p lt2 s f t).
Proof. exact (eq_refl (term453 A B C P p lt2 s t f)). Qed.
Lemma lem8127759 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8127760 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) (z : type517 A B C P) (f : A -> B) : (term461 A B C P p lt2 s t z f) = (term462 A B C P p lt2 s t z f).
Proof. exact (MK_COMB (@lem8127758 A B C P p lt2 s f t) (@lem8127759 A B C P z f)). Qed.
Lemma lem8127761 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term462 A B C P p lt2 s t z f) = (term463 A B C P p lt2 s z f t).
Proof. exact (eq_refl (term462 A B C P p lt2 s t z f)). Qed.
Lemma lem8127762 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term461 A B C P p lt2 s t z f) = (term463 A B C P p lt2 s z f t).
Proof. exact (TRANS (@lem8127760 A B C P p lt2 s t z f) (@lem8127761 A B C P p lt2 s z f t)). Qed.
Lemma lem8127763 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) : (term464 A B C P p lt2 s t z) = (term465 A B C P p lt2 s z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8127762 A B C P p lt2 s z f t)). Qed.
Lemma lem8127764 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8127765 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) : (term466 A B C P p lt2 s t z) = (term467 A B C P p lt2 s z t).
Proof. exact (MK_COMB (@lem8127764 A B) (@lem8127763 A B C P p lt2 s z t)). Qed.
Lemma lem8127766 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term468 A B C P p lt2 s t) = (term469 A B C P p lt2 s t).
Proof. exact (fun_ext (fun z : type517 A B C P => @lem8127765 A B C P p lt2 s z t)). Qed.
Lemma lem8127767 {A B C P : Type'} : (@ex ((A -> B) -> (A -> B) -> C -> P -> A)) = (@ex ((A -> B) -> (A -> B) -> C -> P -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> B) -> C -> P -> A))). Qed.
Lemma lem8127768 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term451 A B C P p lt2 s t) = (term470 A B C P p lt2 s t).
Proof. exact (MK_COMB (@lem8127767 A B C P) (@lem8127766 A B C P p lt2 s t)). Qed.
Lemma lem8127769 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : ((term450 A B C P p lt2 s t) = (term451 A B C P p lt2 s t)) = ((term447 A B C P p lt2 s t) = (term470 A B C P p lt2 s t)).
Proof. exact (MK_COMB (@lem8127757 A B C P p lt2 s t) (@lem8127768 A B C P p lt2 s t)). Qed.
Lemma lem8127770 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term447 A B C P p lt2 s t) = (term470 A B C P p lt2 s t).
Proof. exact (EQ_MP (@lem8127769 A B C P p lt2 s t) (@lem8127744 A B C P p lt2 s t)). Qed.
Lemma lem8127772 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term321 A B C P p lt2 s t) = (term470 A B C P p lt2 s t).
Proof. exact (TRANS (@lem8127740 A B C P p lt2 s t) (@lem8127770 A B C P p lt2 s t)). Qed.
Lemma lem8127773 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : (term215 A B C P p lt2 s t) = (term470 A B C P p lt2 s t).
Proof. exact (TRANS (@lem8127454 A B C P p lt2 s t) (@lem8127772 A B C P p lt2 s t)). Qed.
Lemma lem8127774 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) (h1 : term215 A B C P p lt2 s t) : term470 A B C P p lt2 s t.
Proof. exact (EQ_MP (@lem8127773 A B C P p lt2 s t) (@lem8127387 A B C P p lt2 s t h1)). Qed.
Lemma lem8127783 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term148 A B P lt2 s a f g z) = (term471 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term144 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8127784 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term150 A B P lt2 s a f g) = (term472 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8127783 A B P lt2 s a f g z)). Qed.
Lemma lem8127785 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8127786 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term152 A B P lt2 s a f g) = (term473 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8127785 A) (@lem8127784 A B P lt2 s a f g)). Qed.
Lemma lem8127788 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term104 A B P p g a) = (term104 A B P p g a).
Proof. exact (eq_refl (term104 A B P p g a)). Qed.
Lemma lem8127789 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term154 A B P p lt2 s a f g) = (term474 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8127788 A B P p g a) (@lem8127786 A B P lt2 s a f g)). Qed.
Lemma lem8127791 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term104 A B P p f a) = (term104 A B P p f a).
Proof. exact (eq_refl (term104 A B P p f a)). Qed.
Lemma lem8127844 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term156 A B P p lt2 s a f g) = (term475 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8127791 A B P p f a) (@lem8127789 A B P p lt2 s a f g)). Qed.
Lemma lem8127845 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term475 A B P p lt2 s a f g.
Proof. exact (EQ_MP (@lem8127844 A B P p lt2 s a f g) (@lem8127388 A B P p lt2 s a f g h1)). Qed.
Lemma lem8127864 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term290 A B C P f t g x a) = (term476 A B C P f t g x a).
Proof. exact (@lem17646 (t f x a) (t g x a)). Qed.
Lemma lem8127865 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term290 A B C P f t g x a) : term476 A B C P f t g x a.
Proof. exact (EQ_MP (@lem8127864 A B C P f t g x a) (@lem8127393 A B C P f t g x a h1)). Qed.
Lemma lem8127866 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term467 A B C P p lt2 s z t.
Proof. exact (h1). Qed.
Lemma lem8127867 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8127872 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127873 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8127872 A B f x). Qed.
Lemma lem8127875 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8127873 A B f z). Qed.
Lemma lem8127880 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127881 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8127880 A B f x). Qed.
Lemma lem8127883 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8127881 A B g z). Qed.
Lemma lem8127884 {A B : Type'} (f : A -> B) (z : A) : (term477 A B f z) = (term478 A B f z).
Proof. exact (MK_COMB (@lem8127867 B) (@lem8127875 A B f z)). Qed.
Lemma lem8127885 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8127884 A B f z) (@lem8127883 A B g z)). Qed.
Lemma lem8127886 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8127893 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127894 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8127893 P A f x). Qed.
Lemma lem8127896 {A P : Type'} (s : P -> A) (a : P) : (s a) = (@I (P -> A) s a).
Proof. exact (@lem8127894 A P s a). Qed.
Lemma lem8127897 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8127898 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term144 A P lt2 z s a) = (term479 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8127897 A lt2 z) (@lem8127896 A P s a)). Qed.
Lemma lem8127900 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127901 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8127900 A (A -> Prop) f x). Qed.
Lemma lem8127902 {A : Type'} (lt2 : type1402 A) (z : A) : (lt2 z) = (@I (A -> A -> Prop) lt2 z).
Proof. exact (@lem8127901 A lt2 z). Qed.
Lemma lem8127903 {A P : Type'} (s : P -> A) (a : P) : (@I (P -> A) s a) = (@I (P -> A) s a).
Proof. exact (eq_refl (@I (P -> A) s a)). Qed.
Lemma lem8127904 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term479 A P lt2 z s a) = (term480 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8127902 A lt2 z) (@lem8127903 A P s a)). Qed.
Lemma lem8127906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127907 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8127906 A Prop f x). Qed.
Lemma lem8127908 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term480 A P lt2 z s a) = (term481 A P lt2 z s a).
Proof. exact (@lem8127907 A (@I (A -> A -> Prop) lt2 z) (@I (P -> A) s a)). Qed.
Lemma lem8127909 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term479 A P lt2 z s a) = (term481 A P lt2 z s a).
Proof. exact (TRANS (@lem8127904 A P lt2 z s a) (@lem8127908 A P lt2 z s a)). Qed.
Lemma lem8127910 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term144 A P lt2 z s a) = (term481 A P lt2 z s a).
Proof. exact (TRANS (@lem8127898 A P lt2 z s a) (@lem8127909 A P lt2 z s a)). Qed.
Lemma lem8127911 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term482 A P lt2 z s a) = (term483 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8127886) (@lem8127910 A P lt2 z s a)). Qed.
Lemma lem8127912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8127913 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term484 A P lt2 z s a) = (term485 A P lt2 z s a).
Proof. exact (MK_COMB (@lem8127912) (@lem8127911 A P lt2 z s a)). Qed.
Lemma lem8127914 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term471 A B P lt2 s a f g z) = (term486 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8127913 A P lt2 z s a) (@lem8127885 A B f g z)). Qed.
Lemma lem8127915 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term472 A B P lt2 s a f g) = (term487 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8127914 A B P lt2 s a f g z)). Qed.
Lemma lem8127916 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8127917 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term473 A B P lt2 s a f g) = (term488 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8127916 A) (@lem8127915 A B P lt2 s a f g)). Qed.
Lemma lem8127924 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127925 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8127924 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8127926 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8127925 A B P p g). Qed.
Lemma lem8127927 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8127928 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (@I ((A -> B) -> P -> Prop) p g a).
Proof. exact (MK_COMB (@lem8127926 A B P p g) (@lem8127927 P a)). Qed.
Lemma lem8127930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127931 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8127930 P Prop f x). Qed.
Lemma lem8127932 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p g a) = (term489 A B P p g a).
Proof. exact (@lem8127931 P (@I ((A -> B) -> P -> Prop) p g) a). Qed.
Lemma lem8127934 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (p g a) = (term489 A B P p g a).
Proof. exact (TRANS (@lem8127928 A B P p g a) (@lem8127932 A B P p g a)). Qed.
Lemma lem8127935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8127936 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term104 A B P p g a) = (term490 A B P p g a).
Proof. exact (MK_COMB (@lem8127935) (@lem8127934 A B P p g a)). Qed.
Lemma lem8127937 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term474 A B P p lt2 s a f g) = (term491 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8127936 A B P p g a) (@lem8127917 A B P lt2 s a f g)). Qed.
Lemma lem8127944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127945 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8127944 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8127946 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8127945 A B P p f). Qed.
Lemma lem8127947 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8127948 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (@I ((A -> B) -> P -> Prop) p f a).
Proof. exact (MK_COMB (@lem8127946 A B P p f) (@lem8127947 P a)). Qed.
Lemma lem8127950 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127951 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8127950 P Prop f x). Qed.
Lemma lem8127952 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (@I ((A -> B) -> P -> Prop) p f a) = (term489 A B P p f a).
Proof. exact (@lem8127951 P (@I ((A -> B) -> P -> Prop) p f) a). Qed.
Lemma lem8127954 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (p f a) = (term489 A B P p f a).
Proof. exact (TRANS (@lem8127948 A B P p f a) (@lem8127952 A B P p f a)). Qed.
Lemma lem8127955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8127956 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term104 A B P p f a) = (term490 A B P p f a).
Proof. exact (MK_COMB (@lem8127955) (@lem8127954 A B P p f a)). Qed.
Lemma lem8127957 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term475 A B P p lt2 s a f g) = (term492 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8127956 A B P p f a) (@lem8127937 A B P p lt2 s a f g)). Qed.
Lemma lem8127958 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term492 A B P p lt2 s a f g.
Proof. exact (EQ_MP (@lem8127957 A B P p lt2 s a f g) (@lem8127845 A B P p lt2 s a f g h1)). Qed.
Lemma lem8127967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127968 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8127967 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8127969 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (t g) = (@I ((A -> B) -> C -> P -> Prop) t g).
Proof. exact (@lem8127968 A B C P t g). Qed.
Lemma lem8127970 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8127971 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) : (t g x) = (@I ((A -> B) -> C -> P -> Prop) t g x).
Proof. exact (MK_COMB (@lem8127969 A B C P t g) (@lem8127970 C x)). Qed.
Lemma lem8127973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127974 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8127973 C (P -> Prop) f x). Qed.
Lemma lem8127975 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) : (@I ((A -> B) -> C -> P -> Prop) t g x) = (term493 A B C P t g x).
Proof. exact (@lem8127974 C P (@I ((A -> B) -> C -> P -> Prop) t g) x). Qed.
Lemma lem8127976 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) : (t g x) = (term493 A B C P t g x).
Proof. exact (TRANS (@lem8127971 A B C P t g x) (@lem8127975 A B C P t g x)). Qed.
Lemma lem8127977 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8127978 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (t g x a) = (term494 A B C P t g x a).
Proof. exact (MK_COMB (@lem8127976 A B C P t g x) (@lem8127977 P a)). Qed.
Lemma lem8127980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127981 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8127980 P Prop f x). Qed.
Lemma lem8127982 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term494 A B C P t g x a) = (term495 A B C P t g x a).
Proof. exact (@lem8127981 P (term493 A B C P t g x) a). Qed.
Lemma lem8127984 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (t g x a) = (term495 A B C P t g x a).
Proof. exact (TRANS (@lem8127978 A B C P t g x a) (@lem8127982 A B C P t g x a)). Qed.
Lemma lem8127985 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8127994 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8127995 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8127994 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8127996 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (t f) = (@I ((A -> B) -> C -> P -> Prop) t f).
Proof. exact (@lem8127995 A B C P t f). Qed.
Lemma lem8127997 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8127998 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) : (t f x) = (@I ((A -> B) -> C -> P -> Prop) t f x).
Proof. exact (MK_COMB (@lem8127996 A B C P t f) (@lem8127997 C x)). Qed.
Lemma lem8128000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128001 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8128000 C (P -> Prop) f x). Qed.
Lemma lem8128002 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) : (@I ((A -> B) -> C -> P -> Prop) t f x) = (term493 A B C P t f x).
Proof. exact (@lem8128001 C P (@I ((A -> B) -> C -> P -> Prop) t f) x). Qed.
Lemma lem8128003 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) : (t f x) = (term493 A B C P t f x).
Proof. exact (TRANS (@lem8127998 A B C P t f x) (@lem8128002 A B C P t f x)). Qed.
Lemma lem8128004 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8128005 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (t f x a) = (term494 A B C P t f x a).
Proof. exact (MK_COMB (@lem8128003 A B C P t f x) (@lem8128004 P a)). Qed.
Lemma lem8128007 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128008 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128007 P Prop f x). Qed.
Lemma lem8128009 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term494 A B C P t f x a) = (term495 A B C P t f x a).
Proof. exact (@lem8128008 P (term493 A B C P t f x) a). Qed.
Lemma lem8128011 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (t f x a) = (term495 A B C P t f x a).
Proof. exact (TRANS (@lem8128005 A B C P t f x a) (@lem8128009 A B C P t f x a)). Qed.
Lemma lem8128012 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term496 A B C P t f x a) = (term497 A B C P t f x a).
Proof. exact (MK_COMB (@lem8127985) (@lem8128011 A B C P t f x a)). Qed.
Lemma lem8128013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8128014 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term498 A B C P t f x a) = (term499 A B C P t f x a).
Proof. exact (MK_COMB (@lem8128013) (@lem8128012 A B C P t f x a)). Qed.
Lemma lem8128015 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term500 A B C P f t g x a) = (term501 A B C P f t g x a).
Proof. exact (MK_COMB (@lem8128014 A B C P t f x a) (@lem8127984 A B C P t g x a)). Qed.
Lemma lem8128016 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8128025 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128026 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8128025 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8128027 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (t g) = (@I ((A -> B) -> C -> P -> Prop) t g).
Proof. exact (@lem8128026 A B C P t g). Qed.
Lemma lem8128028 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8128029 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) : (t g x) = (@I ((A -> B) -> C -> P -> Prop) t g x).
Proof. exact (MK_COMB (@lem8128027 A B C P t g) (@lem8128028 C x)). Qed.
Lemma lem8128031 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128032 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8128031 C (P -> Prop) f x). Qed.
Lemma lem8128033 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) : (@I ((A -> B) -> C -> P -> Prop) t g x) = (term493 A B C P t g x).
Proof. exact (@lem8128032 C P (@I ((A -> B) -> C -> P -> Prop) t g) x). Qed.
Lemma lem8128034 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) : (t g x) = (term493 A B C P t g x).
Proof. exact (TRANS (@lem8128029 A B C P t g x) (@lem8128033 A B C P t g x)). Qed.
Lemma lem8128035 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8128036 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (t g x a) = (term494 A B C P t g x a).
Proof. exact (MK_COMB (@lem8128034 A B C P t g x) (@lem8128035 P a)). Qed.
Lemma lem8128038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128039 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128038 P Prop f x). Qed.
Lemma lem8128040 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term494 A B C P t g x a) = (term495 A B C P t g x a).
Proof. exact (@lem8128039 P (term493 A B C P t g x) a). Qed.
Lemma lem8128042 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (t g x a) = (term495 A B C P t g x a).
Proof. exact (TRANS (@lem8128036 A B C P t g x a) (@lem8128040 A B C P t g x a)). Qed.
Lemma lem8128043 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term496 A B C P t g x a) = (term497 A B C P t g x a).
Proof. exact (MK_COMB (@lem8128016) (@lem8128042 A B C P t g x a)). Qed.
Lemma lem8128052 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128053 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8128052 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8128054 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (t f) = (@I ((A -> B) -> C -> P -> Prop) t f).
Proof. exact (@lem8128053 A B C P t f). Qed.
Lemma lem8128055 {C : Type'} (x : C) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8128056 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) : (t f x) = (@I ((A -> B) -> C -> P -> Prop) t f x).
Proof. exact (MK_COMB (@lem8128054 A B C P t f) (@lem8128055 C x)). Qed.
Lemma lem8128058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128059 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8128058 C (P -> Prop) f x). Qed.
Lemma lem8128060 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) : (@I ((A -> B) -> C -> P -> Prop) t f x) = (term493 A B C P t f x).
Proof. exact (@lem8128059 C P (@I ((A -> B) -> C -> P -> Prop) t f) x). Qed.
Lemma lem8128061 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) : (t f x) = (term493 A B C P t f x).
Proof. exact (TRANS (@lem8128056 A B C P t f x) (@lem8128060 A B C P t f x)). Qed.
Lemma lem8128062 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8128063 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (t f x a) = (term494 A B C P t f x a).
Proof. exact (MK_COMB (@lem8128061 A B C P t f x) (@lem8128062 P a)). Qed.
Lemma lem8128065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128066 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128065 P Prop f x). Qed.
Lemma lem8128067 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term494 A B C P t f x a) = (term495 A B C P t f x a).
Proof. exact (@lem8128066 P (term493 A B C P t f x) a). Qed.
Lemma lem8128069 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (t f x a) = (term495 A B C P t f x a).
Proof. exact (TRANS (@lem8128063 A B C P t f x a) (@lem8128067 A B C P t f x a)). Qed.
Lemma lem8128070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8128071 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term502 A B C P t f x a) = (term503 A B C P t f x a).
Proof. exact (MK_COMB (@lem8128070) (@lem8128069 A B C P t f x a)). Qed.
Lemma lem8128072 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term504 A B C P f t g x a) = (term505 A B C P f t g x a).
Proof. exact (MK_COMB (@lem8128071 A B C P t f x a) (@lem8128043 A B C P t g x a)). Qed.
Lemma lem8128073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128074 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term506 A B C P f t g x a) = (term507 A B C P f t g x a).
Proof. exact (MK_COMB (@lem8128073) (@lem8128072 A B C P f t g x a)). Qed.
Lemma lem8128075 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term476 A B C P f t g x a) = (term508 A B C P f t g x a).
Proof. exact (MK_COMB (@lem8128074 A B C P f t g x a) (@lem8128015 A B C P f t g x a)). Qed.
Lemma lem8128076 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term290 A B C P f t g x a) : term508 A B C P f t g x a.
Proof. exact (EQ_MP (@lem8128075 A B C P f t g x a) (@lem8127865 A B C P f t g x a h1)). Qed.
Lemma lem8128085 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128086 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8128085 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8128087 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (t g) = (@I ((A -> B) -> C -> P -> Prop) t g).
Proof. exact (@lem8128086 A B C P t g). Qed.
Lemma lem8128088 {C : Type'} (p1 : C) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8128089 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) : (t g p1) = (@I ((A -> B) -> C -> P -> Prop) t g p1).
Proof. exact (MK_COMB (@lem8128087 A B C P t g) (@lem8128088 C p1)). Qed.
Lemma lem8128091 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128092 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8128091 C (P -> Prop) f x). Qed.
Lemma lem8128093 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) : (@I ((A -> B) -> C -> P -> Prop) t g p1) = (term493 A B C P t g p1).
Proof. exact (@lem8128092 C P (@I ((A -> B) -> C -> P -> Prop) t g) p1). Qed.
Lemma lem8128094 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) : (t g p1) = (term493 A B C P t g p1).
Proof. exact (TRANS (@lem8128089 A B C P t g p1) (@lem8128093 A B C P t g p1)). Qed.
Lemma lem8128095 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128096 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (t g p1 p2) = (term494 A B C P t g p1 p2).
Proof. exact (MK_COMB (@lem8128094 A B C P t g p1) (@lem8128095 P p2)). Qed.
Lemma lem8128098 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128099 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128098 P Prop f x). Qed.
Lemma lem8128100 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term494 A B C P t g p1 p2) = (term495 A B C P t g p1 p2).
Proof. exact (@lem8128099 P (term493 A B C P t g p1) p2). Qed.
Lemma lem8128102 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (t g p1 p2) = (term495 A B C P t g p1 p2).
Proof. exact (TRANS (@lem8128096 A B C P t g p1 p2) (@lem8128100 A B C P t g p1 p2)). Qed.
Lemma lem8128103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8128112 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128113 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8128112 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8128114 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (t f) = (@I ((A -> B) -> C -> P -> Prop) t f).
Proof. exact (@lem8128113 A B C P t f). Qed.
Lemma lem8128115 {C : Type'} (p1 : C) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8128116 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) : (t f p1) = (@I ((A -> B) -> C -> P -> Prop) t f p1).
Proof. exact (MK_COMB (@lem8128114 A B C P t f) (@lem8128115 C p1)). Qed.
Lemma lem8128118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128119 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8128118 C (P -> Prop) f x). Qed.
Lemma lem8128120 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) : (@I ((A -> B) -> C -> P -> Prop) t f p1) = (term493 A B C P t f p1).
Proof. exact (@lem8128119 C P (@I ((A -> B) -> C -> P -> Prop) t f) p1). Qed.
Lemma lem8128121 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) : (t f p1) = (term493 A B C P t f p1).
Proof. exact (TRANS (@lem8128116 A B C P t f p1) (@lem8128120 A B C P t f p1)). Qed.
Lemma lem8128122 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128123 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (t f p1 p2) = (term494 A B C P t f p1 p2).
Proof. exact (MK_COMB (@lem8128121 A B C P t f p1) (@lem8128122 P p2)). Qed.
Lemma lem8128125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128126 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128125 P Prop f x). Qed.
Lemma lem8128127 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term494 A B C P t f p1 p2) = (term495 A B C P t f p1 p2).
Proof. exact (@lem8128126 P (term493 A B C P t f p1) p2). Qed.
Lemma lem8128129 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (t f p1 p2) = (term495 A B C P t f p1 p2).
Proof. exact (TRANS (@lem8128123 A B C P t f p1 p2) (@lem8128127 A B C P t f p1 p2)). Qed.
Lemma lem8128130 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term496 A B C P t f p1 p2) = (term497 A B C P t f p1 p2).
Proof. exact (MK_COMB (@lem8128103) (@lem8128129 A B C P t f p1 p2)). Qed.
Lemma lem8128131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128132 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term509 A B C P t f p1 p2) = (term510 A B C P t f p1 p2).
Proof. exact (MK_COMB (@lem8128131) (@lem8128130 A B C P t f p1 p2)). Qed.
Lemma lem8128133 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term511 A B C P f t g p1 p2) = (term512 A B C P f t g p1 p2).
Proof. exact (MK_COMB (@lem8128132 A B C P t f p1 p2) (@lem8128102 A B C P t g p1 p2)). Qed.
Lemma lem8128134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8128143 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128144 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8128143 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8128145 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) : (t g) = (@I ((A -> B) -> C -> P -> Prop) t g).
Proof. exact (@lem8128144 A B C P t g). Qed.
Lemma lem8128146 {C : Type'} (p1 : C) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8128147 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) : (t g p1) = (@I ((A -> B) -> C -> P -> Prop) t g p1).
Proof. exact (MK_COMB (@lem8128145 A B C P t g) (@lem8128146 C p1)). Qed.
Lemma lem8128149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128150 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8128149 C (P -> Prop) f x). Qed.
Lemma lem8128151 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) : (@I ((A -> B) -> C -> P -> Prop) t g p1) = (term493 A B C P t g p1).
Proof. exact (@lem8128150 C P (@I ((A -> B) -> C -> P -> Prop) t g) p1). Qed.
Lemma lem8128152 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) : (t g p1) = (term493 A B C P t g p1).
Proof. exact (TRANS (@lem8128147 A B C P t g p1) (@lem8128151 A B C P t g p1)). Qed.
Lemma lem8128153 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128154 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (t g p1 p2) = (term494 A B C P t g p1 p2).
Proof. exact (MK_COMB (@lem8128152 A B C P t g p1) (@lem8128153 P p2)). Qed.
Lemma lem8128156 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128157 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128156 P Prop f x). Qed.
Lemma lem8128158 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term494 A B C P t g p1 p2) = (term495 A B C P t g p1 p2).
Proof. exact (@lem8128157 P (term493 A B C P t g p1) p2). Qed.
Lemma lem8128160 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (t g p1 p2) = (term495 A B C P t g p1 p2).
Proof. exact (TRANS (@lem8128154 A B C P t g p1 p2) (@lem8128158 A B C P t g p1 p2)). Qed.
Lemma lem8128161 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term496 A B C P t g p1 p2) = (term497 A B C P t g p1 p2).
Proof. exact (MK_COMB (@lem8128134) (@lem8128160 A B C P t g p1 p2)). Qed.
Lemma lem8128170 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128171 {A B C P : Type'} (f : type554 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> Prop) f x).
Proof. exact (@lem8128170 (A -> B) (type1413 C P) f x). Qed.
Lemma lem8128172 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) : (t f) = (@I ((A -> B) -> C -> P -> Prop) t f).
Proof. exact (@lem8128171 A B C P t f). Qed.
Lemma lem8128173 {C : Type'} (p1 : C) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8128174 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) : (t f p1) = (@I ((A -> B) -> C -> P -> Prop) t f p1).
Proof. exact (MK_COMB (@lem8128172 A B C P t f) (@lem8128173 C p1)). Qed.
Lemma lem8128176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128177 {C P : Type'} (f : type1413 C P) (x : C) : (f x) = (@I (C -> P -> Prop) f x).
Proof. exact (@lem8128176 C (P -> Prop) f x). Qed.
Lemma lem8128178 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) : (@I ((A -> B) -> C -> P -> Prop) t f p1) = (term493 A B C P t f p1).
Proof. exact (@lem8128177 C P (@I ((A -> B) -> C -> P -> Prop) t f) p1). Qed.
Lemma lem8128179 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) : (t f p1) = (term493 A B C P t f p1).
Proof. exact (TRANS (@lem8128174 A B C P t f p1) (@lem8128178 A B C P t f p1)). Qed.
Lemma lem8128180 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128181 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (t f p1 p2) = (term494 A B C P t f p1 p2).
Proof. exact (MK_COMB (@lem8128179 A B C P t f p1) (@lem8128180 P p2)). Qed.
Lemma lem8128183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128184 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128183 P Prop f x). Qed.
Lemma lem8128185 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term494 A B C P t f p1 p2) = (term495 A B C P t f p1 p2).
Proof. exact (@lem8128184 P (term493 A B C P t f p1) p2). Qed.
Lemma lem8128187 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (t f p1 p2) = (term495 A B C P t f p1 p2).
Proof. exact (TRANS (@lem8128181 A B C P t f p1 p2) (@lem8128185 A B C P t f p1 p2)). Qed.
Lemma lem8128188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128189 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (p1 : C) (p2 : P) : (term513 A B C P t f p1 p2) = (term514 A B C P t f p1 p2).
Proof. exact (MK_COMB (@lem8128188) (@lem8128187 A B C P t f p1 p2)). Qed.
Lemma lem8128190 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term515 A B C P f t g p1 p2) = (term516 A B C P f t g p1 p2).
Proof. exact (MK_COMB (@lem8128189 A B C P t f p1 p2) (@lem8128161 A B C P t g p1 p2)). Qed.
Lemma lem8128191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8128192 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term517 A B C P f t g p1 p2) = (term518 A B C P f t g p1 p2).
Proof. exact (MK_COMB (@lem8128191) (@lem8128190 A B C P f t g p1 p2)). Qed.
Lemma lem8128193 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term309 A B C P f t g p1 p2) = (term519 A B C P f t g p1 p2).
Proof. exact (MK_COMB (@lem8128192 A B C P f t g p1 p2) (@lem8128133 A B C P f t g p1 p2)). Qed.
Lemma lem8128194 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8128195 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8128196 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8128207 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128208 {A B C P : Type'} (f : type517 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) f x).
Proof. exact (@lem8128207 (A -> B) (type553 A B C P) f x). Qed.
Lemma lem8128209 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f).
Proof. exact (@lem8128208 A B C P z f). Qed.
Lemma lem8128210 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8128211 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8128209 A B C P z f) (@lem8128210 A B g)). Qed.
Lemma lem8128213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128214 {A B C P : Type'} (f : type553 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> A) f x).
Proof. exact (@lem8128213 (A -> B) (type1475 A C P) f x). Qed.
Lemma lem8128215 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f g) = (term520 A B C P z f g).
Proof. exact (@lem8128214 A B C P (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f) g). Qed.
Lemma lem8128216 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (z f g) = (term520 A B C P z f g).
Proof. exact (TRANS (@lem8128211 A B C P z f g) (@lem8128215 A B C P z f g)). Qed.
Lemma lem8128217 {C : Type'} (p1 : C) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8128218 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (z f g p1) = (term521 A B C P z f g p1).
Proof. exact (MK_COMB (@lem8128216 A B C P z f g) (@lem8128217 C p1)). Qed.
Lemma lem8128220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128221 {A C P : Type'} (f : type1475 A C P) (x : C) : (f x) = (@I (C -> P -> A) f x).
Proof. exact (@lem8128220 C (P -> A) f x). Qed.
Lemma lem8128222 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (term521 A B C P z f g p1) = (term522 A B C P z f g p1).
Proof. exact (@lem8128221 A C P (term520 A B C P z f g) p1). Qed.
Lemma lem8128223 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (z f g p1) = (term522 A B C P z f g p1).
Proof. exact (TRANS (@lem8128218 A B C P z f g p1) (@lem8128222 A B C P z f g p1)). Qed.
Lemma lem8128224 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128225 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (z f g p1 p2) = (term523 A B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8128223 A B C P z f g p1) (@lem8128224 P p2)). Qed.
Lemma lem8128227 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128228 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8128227 P A f x). Qed.
Lemma lem8128229 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term523 A B C P z f g p1 p2) = (term524 A B C P z f g p1 p2).
Proof. exact (@lem8128228 A P (term522 A B C P z f g p1) p2). Qed.
Lemma lem8128231 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (z f g p1 p2) = (term524 A B C P z f g p1 p2).
Proof. exact (TRANS (@lem8128225 A B C P z f g p1 p2) (@lem8128229 A B C P z f g p1 p2)). Qed.
Lemma lem8128232 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term525 A B C P z f g p1 p2) = (term526 A B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8128196 A B f) (@lem8128231 A B C P z f g p1 p2)). Qed.
Lemma lem8128234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128235 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8128234 A B f x). Qed.
Lemma lem8128236 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term526 A B C P z f g p1 p2) = (term527 A B C P z f g p1 p2).
Proof. exact (@lem8128235 A B f (term524 A B C P z f g p1 p2)). Qed.
Lemma lem8128237 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term525 A B C P z f g p1 p2) = (term527 A B C P z f g p1 p2).
Proof. exact (TRANS (@lem8128232 A B C P z f g p1 p2) (@lem8128236 A B C P z f g p1 p2)). Qed.
Lemma lem8128238 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8128249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128250 {A B C P : Type'} (f : type517 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) f x).
Proof. exact (@lem8128249 (A -> B) (type553 A B C P) f x). Qed.
Lemma lem8128251 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f).
Proof. exact (@lem8128250 A B C P z f). Qed.
Lemma lem8128252 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8128253 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8128251 A B C P z f) (@lem8128252 A B g)). Qed.
Lemma lem8128255 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128256 {A B C P : Type'} (f : type553 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> A) f x).
Proof. exact (@lem8128255 (A -> B) (type1475 A C P) f x). Qed.
Lemma lem8128257 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f g) = (term520 A B C P z f g).
Proof. exact (@lem8128256 A B C P (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f) g). Qed.
Lemma lem8128258 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (z f g) = (term520 A B C P z f g).
Proof. exact (TRANS (@lem8128253 A B C P z f g) (@lem8128257 A B C P z f g)). Qed.
Lemma lem8128259 {C : Type'} (p1 : C) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8128260 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (z f g p1) = (term521 A B C P z f g p1).
Proof. exact (MK_COMB (@lem8128258 A B C P z f g) (@lem8128259 C p1)). Qed.
Lemma lem8128262 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128263 {A C P : Type'} (f : type1475 A C P) (x : C) : (f x) = (@I (C -> P -> A) f x).
Proof. exact (@lem8128262 C (P -> A) f x). Qed.
Lemma lem8128264 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (term521 A B C P z f g p1) = (term522 A B C P z f g p1).
Proof. exact (@lem8128263 A C P (term520 A B C P z f g) p1). Qed.
Lemma lem8128265 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (z f g p1) = (term522 A B C P z f g p1).
Proof. exact (TRANS (@lem8128260 A B C P z f g p1) (@lem8128264 A B C P z f g p1)). Qed.
Lemma lem8128266 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128267 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (z f g p1 p2) = (term523 A B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8128265 A B C P z f g p1) (@lem8128266 P p2)). Qed.
Lemma lem8128269 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128270 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8128269 P A f x). Qed.
Lemma lem8128271 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term523 A B C P z f g p1 p2) = (term524 A B C P z f g p1 p2).
Proof. exact (@lem8128270 A P (term522 A B C P z f g p1) p2). Qed.
Lemma lem8128273 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (z f g p1 p2) = (term524 A B C P z f g p1 p2).
Proof. exact (TRANS (@lem8128267 A B C P z f g p1 p2) (@lem8128271 A B C P z f g p1 p2)). Qed.
Lemma lem8128274 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term528 A B C P z f g p1 p2) = (term529 A B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8128238 A B g) (@lem8128273 A B C P z f g p1 p2)). Qed.
Lemma lem8128276 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128277 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8128276 A B f x). Qed.
Lemma lem8128278 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term529 A B C P z f g p1 p2) = (term530 A B C P z f g p1 p2).
Proof. exact (@lem8128277 A B g (term524 A B C P z f g p1 p2)). Qed.
Lemma lem8128279 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term528 A B C P z f g p1 p2) = (term530 A B C P z f g p1 p2).
Proof. exact (TRANS (@lem8128274 A B C P z f g p1 p2) (@lem8128278 A B C P z f g p1 p2)). Qed.
Lemma lem8128280 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term531 A B C P z f g p1 p2) = (term532 A B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8128195 B) (@lem8128237 A B C P z f g p1 p2)). Qed.
Lemma lem8128281 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : ((term525 A B C P z f g p1 p2) = (term528 A B C P z f g p1 p2)) = ((term527 A B C P z f g p1 p2) = (term530 A B C P z f g p1 p2)).
Proof. exact (MK_COMB (@lem8128280 A B C P z f g p1 p2) (@lem8128279 A B C P z f g p1 p2)). Qed.
Lemma lem8128282 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term533 A B C P z f g p1 p2) = (term534 A B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8128194) (@lem8128281 A B C P z f g p1 p2)). Qed.
Lemma lem8128283 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8128294 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128295 {A B C P : Type'} (f : type517 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) f x).
Proof. exact (@lem8128294 (A -> B) (type553 A B C P) f x). Qed.
Lemma lem8128296 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) : (z f) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f).
Proof. exact (@lem8128295 A B C P z f). Qed.
Lemma lem8128297 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8128298 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (z f g) = (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f g).
Proof. exact (MK_COMB (@lem8128296 A B C P z f) (@lem8128297 A B g)). Qed.
Lemma lem8128300 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128301 {A B C P : Type'} (f : type553 A B C P) (x : A -> B) : (f x) = (@I ((A -> B) -> C -> P -> A) f x).
Proof. exact (@lem8128300 (A -> B) (type1475 A C P) f x). Qed.
Lemma lem8128302 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f g) = (term520 A B C P z f g).
Proof. exact (@lem8128301 A B C P (@I ((A -> B) -> (A -> B) -> C -> P -> A) z f) g). Qed.
Lemma lem8128303 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) : (z f g) = (term520 A B C P z f g).
Proof. exact (TRANS (@lem8128298 A B C P z f g) (@lem8128302 A B C P z f g)). Qed.
Lemma lem8128304 {C : Type'} (p1 : C) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8128305 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (z f g p1) = (term521 A B C P z f g p1).
Proof. exact (MK_COMB (@lem8128303 A B C P z f g) (@lem8128304 C p1)). Qed.
Lemma lem8128307 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128308 {A C P : Type'} (f : type1475 A C P) (x : C) : (f x) = (@I (C -> P -> A) f x).
Proof. exact (@lem8128307 C (P -> A) f x). Qed.
Lemma lem8128309 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (term521 A B C P z f g p1) = (term522 A B C P z f g p1).
Proof. exact (@lem8128308 A C P (term520 A B C P z f g) p1). Qed.
Lemma lem8128310 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) : (z f g p1) = (term522 A B C P z f g p1).
Proof. exact (TRANS (@lem8128305 A B C P z f g p1) (@lem8128309 A B C P z f g p1)). Qed.
Lemma lem8128311 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128312 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (z f g p1 p2) = (term523 A B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8128310 A B C P z f g p1) (@lem8128311 P p2)). Qed.
Lemma lem8128314 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128315 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8128314 P A f x). Qed.
Lemma lem8128316 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term523 A B C P z f g p1 p2) = (term524 A B C P z f g p1 p2).
Proof. exact (@lem8128315 A P (term522 A B C P z f g p1) p2). Qed.
Lemma lem8128318 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (z f g p1 p2) = (term524 A B C P z f g p1 p2).
Proof. exact (TRANS (@lem8128312 A B C P z f g p1 p2) (@lem8128316 A B C P z f g p1 p2)). Qed.
Lemma lem8128323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128324 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8128323 P A f x). Qed.
Lemma lem8128326 {A P : Type'} (s : P -> A) (p2 : P) : (s p2) = (@I (P -> A) s p2).
Proof. exact (@lem8128324 A P s p2). Qed.
Lemma lem8128327 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term535 A B C P lt2 z f g p1 p2) = (term536 A B C P lt2 z f g p1 p2).
Proof. exact (MK_COMB (@lem8128283 A lt2) (@lem8128318 A B C P z f g p1 p2)). Qed.
Lemma lem8128328 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (s : P -> A) (p2 : P) : (term537 A B C P lt2 z f g p1 s p2) = (term538 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8128327 A B C P lt2 z f g p1 p2) (@lem8128326 A P s p2)). Qed.
Lemma lem8128330 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128331 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem8128330 A (A -> Prop) f x). Qed.
Lemma lem8128332 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term536 A B C P lt2 z f g p1 p2) = (term539 A B C P lt2 z f g p1 p2).
Proof. exact (@lem8128331 A lt2 (term524 A B C P z f g p1 p2)). Qed.
Lemma lem8128333 {A P : Type'} (s : P -> A) (p2 : P) : (@I (P -> A) s p2) = (@I (P -> A) s p2).
Proof. exact (eq_refl (@I (P -> A) s p2)). Qed.
Lemma lem8128334 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (s : P -> A) (p2 : P) : (term538 A B C P lt2 z f g p1 s p2) = (term540 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8128332 A B C P lt2 z f g p1 p2) (@lem8128333 A P s p2)). Qed.
Lemma lem8128336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128337 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8128336 A Prop f x). Qed.
Lemma lem8128338 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (s : P -> A) (p2 : P) : (term540 A B C P lt2 z f g p1 s p2) = (term541 A B C P lt2 z f g p1 s p2).
Proof. exact (@lem8128337 A (term539 A B C P lt2 z f g p1 p2) (@I (P -> A) s p2)). Qed.
Lemma lem8128339 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (s : P -> A) (p2 : P) : (term538 A B C P lt2 z f g p1 s p2) = (term541 A B C P lt2 z f g p1 s p2).
Proof. exact (TRANS (@lem8128334 A B C P lt2 z f g p1 s p2) (@lem8128338 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8128340 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (s : P -> A) (p2 : P) : (term537 A B C P lt2 z f g p1 s p2) = (term541 A B C P lt2 z f g p1 s p2).
Proof. exact (TRANS (@lem8128328 A B C P lt2 z f g p1 s p2) (@lem8128339 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8128341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8128342 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (s : P -> A) (p2 : P) : (term542 A B C P lt2 z f g p1 s p2) = (term543 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8128341) (@lem8128340 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8128343 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term544 A B C P lt2 s z f g p1 p2) = (term545 A B C P lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8128342 A B C P lt2 z f g p1 s p2) (@lem8128282 A B C P z f g p1 p2)). Qed.
Lemma lem8128344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8128351 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128352 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8128351 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8128353 {A B P : Type'} (p : type560 A B P) (g : A -> B) : (p g) = (@I ((A -> B) -> P -> Prop) p g).
Proof. exact (@lem8128352 A B P p g). Qed.
Lemma lem8128354 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128355 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (p g p2) = (@I ((A -> B) -> P -> Prop) p g p2).
Proof. exact (MK_COMB (@lem8128353 A B P p g) (@lem8128354 P p2)). Qed.
Lemma lem8128357 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128358 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128357 P Prop f x). Qed.
Lemma lem8128359 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (@I ((A -> B) -> P -> Prop) p g p2) = (term489 A B P p g p2).
Proof. exact (@lem8128358 P (@I ((A -> B) -> P -> Prop) p g) p2). Qed.
Lemma lem8128361 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (p g p2) = (term489 A B P p g p2).
Proof. exact (TRANS (@lem8128355 A B P p g p2) (@lem8128359 A B P p g p2)). Qed.
Lemma lem8128362 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (term326 A B P p g p2) = (term546 A B P p g p2).
Proof. exact (MK_COMB (@lem8128344) (@lem8128361 A B P p g p2)). Qed.
Lemma lem8128363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128364 {A B P : Type'} (p : type560 A B P) (g : A -> B) (p2 : P) : (term302 A B P p g p2) = (term547 A B P p g p2).
Proof. exact (MK_COMB (@lem8128363) (@lem8128362 A B P p g p2)). Qed.
Lemma lem8128365 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term548 A B C P p lt2 s z f g p1 p2) = (term549 A B C P p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8128364 A B P p g p2) (@lem8128343 A B C P lt2 s z f g p1 p2)). Qed.
Lemma lem8128366 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8128373 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128374 {A B P : Type'} (f : type560 A B P) (x : A -> B) : (f x) = (@I ((A -> B) -> P -> Prop) f x).
Proof. exact (@lem8128373 (A -> B) (P -> Prop) f x). Qed.
Lemma lem8128375 {A B P : Type'} (p : type560 A B P) (f : A -> B) : (p f) = (@I ((A -> B) -> P -> Prop) p f).
Proof. exact (@lem8128374 A B P p f). Qed.
Lemma lem8128376 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8128377 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (p f p2) = (@I ((A -> B) -> P -> Prop) p f p2).
Proof. exact (MK_COMB (@lem8128375 A B P p f) (@lem8128376 P p2)). Qed.
Lemma lem8128379 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8128380 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8128379 P Prop f x). Qed.
Lemma lem8128381 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (@I ((A -> B) -> P -> Prop) p f p2) = (term489 A B P p f p2).
Proof. exact (@lem8128380 P (@I ((A -> B) -> P -> Prop) p f) p2). Qed.
Lemma lem8128383 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (p f p2) = (term489 A B P p f p2).
Proof. exact (TRANS (@lem8128377 A B P p f p2) (@lem8128381 A B P p f p2)). Qed.
Lemma lem8128384 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term326 A B P p f p2) = (term546 A B P p f p2).
Proof. exact (MK_COMB (@lem8128366) (@lem8128383 A B P p f p2)). Qed.
Lemma lem8128385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128386 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term302 A B P p f p2) = (term547 A B P p f p2).
Proof. exact (MK_COMB (@lem8128385) (@lem8128384 A B P p f p2)). Qed.
Lemma lem8128387 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term550 A B C P p lt2 s z f g p1 p2) = (term551 A B C P p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8128386 A B P p f p2) (@lem8128365 A B C P p lt2 s z f g p1 p2)). Qed.
Lemma lem8128388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128389 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term552 A B C P p lt2 s z f g p1 p2) = (term553 A B C P p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8128388) (@lem8128387 A B C P p lt2 s z f g p1 p2)). Qed.
Lemma lem8128390 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term554 A B C P p lt2 s z f t g p1 p2) = (term555 A B C P p lt2 s z f t g p1 p2).
Proof. exact (MK_COMB (@lem8128389 A B C P p lt2 s z f g p1 p2) (@lem8128193 A B C P f t g p1 p2)). Qed.
Lemma lem8128391 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term556 A B C P p lt2 s z f t g p1) = (term557 A B C P p lt2 s z f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8128390 A B C P p lt2 s z f t g p1 p2)). Qed.
Lemma lem8128392 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8128393 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term558 A B C P p lt2 s z f t g p1) = (term559 A B C P p lt2 s z f t g p1).
Proof. exact (MK_COMB (@lem8128392 P) (@lem8128391 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8128394 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term560 A B C P p lt2 s z f t g) = (term561 A B C P p lt2 s z f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8128393 A B C P p lt2 s z f t g p1)). Qed.
Lemma lem8128395 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8128396 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term562 A B C P p lt2 s z f t g) = (term563 A B C P p lt2 s z f t g).
Proof. exact (MK_COMB (@lem8128395 C) (@lem8128394 A B C P p lt2 s z f t g)). Qed.
Lemma lem8128397 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term564 A B C P p lt2 s z f t) = (term565 A B C P p lt2 s z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8128396 A B C P p lt2 s z f t g)). Qed.
Lemma lem8128398 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8128399 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term463 A B C P p lt2 s z f t) = (term566 A B C P p lt2 s z f t).
Proof. exact (MK_COMB (@lem8128398 A B) (@lem8128397 A B C P p lt2 s z f t)). Qed.
Lemma lem8128400 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) : (term465 A B C P p lt2 s z t) = (term567 A B C P p lt2 s z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8128399 A B C P p lt2 s z f t)). Qed.
Lemma lem8128401 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8128402 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) : (term467 A B C P p lt2 s z t) = (term568 A B C P p lt2 s z t).
Proof. exact (MK_COMB (@lem8128401 A B) (@lem8128400 A B C P p lt2 s z t)). Qed.
Lemma lem8128403 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term568 A B C P p lt2 s z t.
Proof. exact (EQ_MP (@lem8128402 A B C P p lt2 s z t) (@lem8127866 A B C P p lt2 s z t h1)). Qed.
Lemma lem8128404 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term491 A B P p lt2 s a f g.
Proof. exact (proj2 (@lem8127958 A B P p lt2 s a f g h1)). Qed.
Lemma lem8128406 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term488 A B P lt2 s a f g.
Proof. exact (proj2 (@lem8128404 A B P p lt2 s a f g h1)). Qed.
Lemma lem8128408 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term505 A B C P f t g x a.
Proof. exact (h1). Qed.
Lemma lem8128409 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term501 A B C P f t g x a.
Proof. exact (h1). Qed.
Lemma lem8128431 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term519 A B C P f t g p1 p2) = (term519 A B C P f t g p1 p2).
Proof. exact (eq_refl (term519 A B C P f t g p1 p2)). Qed.
Lemma lem8128448 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term549 A B C P p lt2 s z f g p1 p2) = (term569 A B C P lt2 s p z f g p1 p2).
Proof. exact (@lem19490 (term541 A B C P lt2 z f g p1 s p2) (term546 A B P p g p2) (term534 A B C P z f g p1 p2)). Qed.
Lemma lem8128451 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term547 A B P p f p2) = (term547 A B P p f p2).
Proof. exact (eq_refl (term547 A B P p f p2)). Qed.
Lemma lem8128452 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term551 A B C P p lt2 s z f g p1 p2) = (term570 A B C P lt2 s p z f g p1 p2).
Proof. exact (MK_COMB (@lem8128451 A B P p f p2) (@lem8128448 A B C P lt2 s p z f g p1 p2)). Qed.
Lemma lem8128459 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term570 A B C P lt2 s p z f g p1 p2) = (term571 A B C P lt2 s p z f g p1 p2).
Proof. exact (@lem19490 (term572 A B C P p lt2 z f g p1 s p2) (term546 A B P p f p2) (term573 A B C P p z f g p1 p2)). Qed.
Lemma lem8128460 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term551 A B C P p lt2 s z f g p1 p2) = (term571 A B C P lt2 s p z f g p1 p2).
Proof. exact (TRANS (@lem8128452 A B C P lt2 s p z f g p1 p2) (@lem8128459 A B C P lt2 s p z f g p1 p2)). Qed.
Lemma lem8128461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128462 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term553 A B C P p lt2 s z f g p1 p2) = (term574 A B C P lt2 s p z f g p1 p2).
Proof. exact (MK_COMB (@lem8128461) (@lem8128460 A B C P lt2 s p z f g p1 p2)). Qed.
Lemma lem8128463 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term555 A B C P p lt2 s z f t g p1 p2) = (term575 A B C P lt2 s p z f t g p1 p2).
Proof. exact (MK_COMB (@lem8128462 A B C P lt2 s p z f g p1 p2) (@lem8128431 A B C P f t g p1 p2)). Qed.
Lemma lem8128464 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term575 A B C P lt2 s p z f t g p1 p2) = (term576 A B C P lt2 s p z f t g p1 p2).
Proof. exact (@lem19490 (term516 A B C P f t g p1 p2) (term571 A B C P lt2 s p z f g p1 p2) (term512 A B C P f t g p1 p2)). Qed.
Lemma lem8128471 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term577 A B C P lt2 s p z f t g p1 p2) = (term578 A B C P lt2 s p z f t g p1 p2).
Proof. exact (@lem19699 (term579 A B C P p lt2 z f g p1 s p2) (term580 A B C P p z f g p1 p2) (term512 A B C P f t g p1 p2)). Qed.
Lemma lem8128478 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term581 A B C P lt2 s p z f t g p1 p2) = (term582 A B C P lt2 s p z f t g p1 p2).
Proof. exact (@lem19699 (term579 A B C P p lt2 z f g p1 s p2) (term580 A B C P p z f g p1 p2) (term516 A B C P f t g p1 p2)). Qed.
Lemma lem8128479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8128480 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term583 A B C P lt2 s p z f t g p1 p2) = (term584 A B C P lt2 s p z f t g p1 p2).
Proof. exact (MK_COMB (@lem8128479) (@lem8128478 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128481 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term576 A B C P lt2 s p z f t g p1 p2) = (term585 A B C P lt2 s p z f t g p1 p2).
Proof. exact (MK_COMB (@lem8128480 A B C P lt2 s p z f t g p1 p2) (@lem8128471 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128482 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term575 A B C P lt2 s p z f t g p1 p2) = (term585 A B C P lt2 s p z f t g p1 p2).
Proof. exact (TRANS (@lem8128464 A B C P lt2 s p z f t g p1 p2) (@lem8128481 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128483 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term555 A B C P p lt2 s z f t g p1 p2) = (term585 A B C P lt2 s p z f t g p1 p2).
Proof. exact (TRANS (@lem8128463 A B C P lt2 s p z f t g p1 p2) (@lem8128482 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128484 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term557 A B C P p lt2 s z f t g p1) = (term586 A B C P lt2 s p z f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8128483 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128485 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8128486 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term559 A B C P p lt2 s z f t g p1) = (term587 A B C P lt2 s p z f t g p1).
Proof. exact (MK_COMB (@lem8128485 P) (@lem8128484 A B C P lt2 s p z f t g p1)). Qed.
Lemma lem8128487 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term561 A B C P p lt2 s z f t g) = (term588 A B C P lt2 s p z f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8128486 A B C P lt2 s p z f t g p1)). Qed.
Lemma lem8128488 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8128489 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term563 A B C P p lt2 s z f t g) = (term589 A B C P lt2 s p z f t g).
Proof. exact (MK_COMB (@lem8128488 C) (@lem8128487 A B C P lt2 s p z f t g)). Qed.
Lemma lem8128490 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term565 A B C P p lt2 s z f t) = (term590 A B C P lt2 s p z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8128489 A B C P lt2 s p z f t g)). Qed.
Lemma lem8128491 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8128492 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term566 A B C P p lt2 s z f t) = (term591 A B C P lt2 s p z f t).
Proof. exact (MK_COMB (@lem8128491 A B) (@lem8128490 A B C P lt2 s p z f t)). Qed.
Lemma lem8128493 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (t : type554 A B C P) : (term567 A B C P p lt2 s z t) = (term592 A B C P lt2 s p z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8128492 A B C P lt2 s p z f t)). Qed.
Lemma lem8128494 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8128496 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (t : type554 A B C P) : (term568 A B C P p lt2 s z t) = (term593 A B C P lt2 s p z t).
Proof. exact (MK_COMB (@lem8128494 A B) (@lem8128493 A B C P lt2 s p z t)). Qed.
Lemma lem8128497 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term593 A B C P lt2 s p z t.
Proof. exact (EQ_MP (@lem8128496 A B C P lt2 s p z t) (@lem8128403 A B C P p lt2 s z t h1)). Qed.
Lemma lem8128513 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term486 A B P lt2 s a f g z) = (term486 A B P lt2 s a f g z).
Proof. exact (eq_refl (term486 A B P lt2 s a f g z)). Qed.
Lemma lem8128514 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term487 A B P lt2 s a f g) = (term487 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8128513 A B P lt2 s a f g z)). Qed.
Lemma lem8128515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8128517 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term488 A B P lt2 s a f g) = (term488 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8128515 A) (@lem8128514 A B P lt2 s a f g)). Qed.
Lemma lem8128518 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term488 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8128517 A B P lt2 s a f g) (@lem8128406 A B P p lt2 s a f g h1)). Qed.
Lemma lem8128544 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term519 A B C P f t g p1 p2) = (term519 A B C P f t g p1 p2).
Proof. exact (eq_refl (term519 A B C P f t g p1 p2)). Qed.
Lemma lem8128561 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term549 A B C P p lt2 s z f g p1 p2) = (term569 A B C P lt2 s p z f g p1 p2).
Proof. exact (@lem19490 (term541 A B C P lt2 z f g p1 s p2) (term546 A B P p g p2) (term534 A B C P z f g p1 p2)). Qed.
Lemma lem8128564 {A B P : Type'} (p : type560 A B P) (f : A -> B) (p2 : P) : (term547 A B P p f p2) = (term547 A B P p f p2).
Proof. exact (eq_refl (term547 A B P p f p2)). Qed.
Lemma lem8128565 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term551 A B C P p lt2 s z f g p1 p2) = (term570 A B C P lt2 s p z f g p1 p2).
Proof. exact (MK_COMB (@lem8128564 A B P p f p2) (@lem8128561 A B C P lt2 s p z f g p1 p2)). Qed.
Lemma lem8128572 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term570 A B C P lt2 s p z f g p1 p2) = (term571 A B C P lt2 s p z f g p1 p2).
Proof. exact (@lem19490 (term572 A B C P p lt2 z f g p1 s p2) (term546 A B P p f p2) (term573 A B C P p z f g p1 p2)). Qed.
Lemma lem8128573 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term551 A B C P p lt2 s z f g p1 p2) = (term571 A B C P lt2 s p z f g p1 p2).
Proof. exact (TRANS (@lem8128565 A B C P lt2 s p z f g p1 p2) (@lem8128572 A B C P lt2 s p z f g p1 p2)). Qed.
Lemma lem8128574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8128575 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (g : A -> B) (p1 : C) (p2 : P) : (term553 A B C P p lt2 s z f g p1 p2) = (term574 A B C P lt2 s p z f g p1 p2).
Proof. exact (MK_COMB (@lem8128574) (@lem8128573 A B C P lt2 s p z f g p1 p2)). Qed.
Lemma lem8128576 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term555 A B C P p lt2 s z f t g p1 p2) = (term575 A B C P lt2 s p z f t g p1 p2).
Proof. exact (MK_COMB (@lem8128575 A B C P lt2 s p z f g p1 p2) (@lem8128544 A B C P f t g p1 p2)). Qed.
Lemma lem8128577 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term575 A B C P lt2 s p z f t g p1 p2) = (term576 A B C P lt2 s p z f t g p1 p2).
Proof. exact (@lem19490 (term516 A B C P f t g p1 p2) (term571 A B C P lt2 s p z f g p1 p2) (term512 A B C P f t g p1 p2)). Qed.
Lemma lem8128584 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term577 A B C P lt2 s p z f t g p1 p2) = (term578 A B C P lt2 s p z f t g p1 p2).
Proof. exact (@lem19699 (term579 A B C P p lt2 z f g p1 s p2) (term580 A B C P p z f g p1 p2) (term512 A B C P f t g p1 p2)). Qed.
Lemma lem8128591 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term581 A B C P lt2 s p z f t g p1 p2) = (term582 A B C P lt2 s p z f t g p1 p2).
Proof. exact (@lem19699 (term579 A B C P p lt2 z f g p1 s p2) (term580 A B C P p z f g p1 p2) (term516 A B C P f t g p1 p2)). Qed.
Lemma lem8128592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8128593 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term583 A B C P lt2 s p z f t g p1 p2) = (term584 A B C P lt2 s p z f t g p1 p2).
Proof. exact (MK_COMB (@lem8128592) (@lem8128591 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128594 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term576 A B C P lt2 s p z f t g p1 p2) = (term585 A B C P lt2 s p z f t g p1 p2).
Proof. exact (MK_COMB (@lem8128593 A B C P lt2 s p z f t g p1 p2) (@lem8128584 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128595 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term575 A B C P lt2 s p z f t g p1 p2) = (term585 A B C P lt2 s p z f t g p1 p2).
Proof. exact (TRANS (@lem8128577 A B C P lt2 s p z f t g p1 p2) (@lem8128594 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128596 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) (p2 : P) : (term555 A B C P p lt2 s z f t g p1 p2) = (term585 A B C P lt2 s p z f t g p1 p2).
Proof. exact (TRANS (@lem8128576 A B C P lt2 s p z f t g p1 p2) (@lem8128595 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128597 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term557 A B C P p lt2 s z f t g p1) = (term586 A B C P lt2 s p z f t g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8128596 A B C P lt2 s p z f t g p1 p2)). Qed.
Lemma lem8128598 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8128599 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) (p1 : C) : (term559 A B C P p lt2 s z f t g p1) = (term587 A B C P lt2 s p z f t g p1).
Proof. exact (MK_COMB (@lem8128598 P) (@lem8128597 A B C P lt2 s p z f t g p1)). Qed.
Lemma lem8128600 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term561 A B C P p lt2 s z f t g) = (term588 A B C P lt2 s p z f t g).
Proof. exact (fun_ext (fun p1 : C => @lem8128599 A B C P lt2 s p z f t g p1)). Qed.
Lemma lem8128601 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem8128602 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) (g : A -> B) : (term563 A B C P p lt2 s z f t g) = (term589 A B C P lt2 s p z f t g).
Proof. exact (MK_COMB (@lem8128601 C) (@lem8128600 A B C P lt2 s p z f t g)). Qed.
Lemma lem8128603 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term565 A B C P p lt2 s z f t) = (term590 A B C P lt2 s p z f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8128602 A B C P lt2 s p z f t g)). Qed.
Lemma lem8128604 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8128605 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (f : A -> B) (t : type554 A B C P) : (term566 A B C P p lt2 s z f t) = (term591 A B C P lt2 s p z f t).
Proof. exact (MK_COMB (@lem8128604 A B) (@lem8128603 A B C P lt2 s p z f t)). Qed.
Lemma lem8128606 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (t : type554 A B C P) : (term567 A B C P p lt2 s z t) = (term592 A B C P lt2 s p z t).
Proof. exact (fun_ext (fun f : A -> B => @lem8128605 A B C P lt2 s p z f t)). Qed.
Lemma lem8128607 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8128609 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (t : type554 A B C P) : (term568 A B C P p lt2 s z t) = (term593 A B C P lt2 s p z t).
Proof. exact (MK_COMB (@lem8128607 A B) (@lem8128606 A B C P lt2 s p z t)). Qed.
Lemma lem8128610 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term593 A B C P lt2 s p z t.
Proof. exact (EQ_MP (@lem8128609 A B C P lt2 s p z t) (@lem8128403 A B C P p lt2 s z t h1)). Qed.
Lemma lem8128626 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term486 A B P lt2 s a f g z) = (term486 A B P lt2 s a f g z).
Proof. exact (eq_refl (term486 A B P lt2 s a f g z)). Qed.
Lemma lem8128627 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term487 A B P lt2 s a f g) = (term487 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8128626 A B P lt2 s a f g z)). Qed.
Lemma lem8128628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8128630 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term488 A B P lt2 s a f g) = (term488 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8128628 A) (@lem8128627 A B P lt2 s a f g)). Qed.
Lemma lem8128631 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term488 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8128630 A B P lt2 s a f g) (@lem8128406 A B P p lt2 s a f g h1)). Qed.
Lemma lem8128640 {A B C P : Type'} (_107628 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term594 A B C P lt2 s p z t _107628.
Proof. exact (@lem8128497 A B C P p lt2 s z t h1 _107628). Qed.
Lemma lem8128641 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) : (term594 A B C P lt2 s p z t _107628) = (term591 A B C P lt2 s p z _107628 t).
Proof. exact (eq_refl (term594 A B C P lt2 s p z t _107628)). Qed.
Lemma lem8128642 {A B C P : Type'} (_107628 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term591 A B C P lt2 s p z _107628 t.
Proof. exact (EQ_MP (@lem8128641 A B C P lt2 s p z _107628 t) (@lem8128640 A B C P _107628 p lt2 s z t h1)). Qed.
Lemma lem8128643 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term595 A B C P lt2 s p z _107628 t _107629.
Proof. exact (@lem8128642 A B C P _107628 p lt2 s z t h1 _107629). Qed.
Lemma lem8128644 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) : (term595 A B C P lt2 s p z _107628 t _107629) = (term589 A B C P lt2 s p z _107628 t _107629).
Proof. exact (eq_refl (term595 A B C P lt2 s p z _107628 t _107629)). Qed.
Lemma lem8128645 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term589 A B C P lt2 s p z _107628 t _107629.
Proof. exact (EQ_MP (@lem8128644 A B C P lt2 s p z _107628 t _107629) (@lem8128643 A B C P _107628 _107629 p lt2 s z t h1)). Qed.
Lemma lem8128646 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term596 A B C P lt2 s p z _107628 t _107629 _107630.
Proof. exact (@lem8128645 A B C P _107628 _107629 p lt2 s z t h1 _107630). Qed.
Lemma lem8128647 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) : (term596 A B C P lt2 s p z _107628 t _107629 _107630) = (term587 A B C P lt2 s p z _107628 t _107629 _107630).
Proof. exact (eq_refl (term596 A B C P lt2 s p z _107628 t _107629 _107630)). Qed.
Lemma lem8128648 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term587 A B C P lt2 s p z _107628 t _107629 _107630.
Proof. exact (EQ_MP (@lem8128647 A B C P lt2 s p z _107628 t _107629 _107630) (@lem8128646 A B C P _107628 _107629 _107630 p lt2 s z t h1)). Qed.
Lemma lem8128649 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term597 A B C P lt2 s p z _107628 t _107629 _107630 _107631.
Proof. exact (@lem8128648 A B C P _107628 _107629 _107630 p lt2 s z t h1 _107631). Qed.
Lemma lem8128650 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term597 A B C P lt2 s p z _107628 t _107629 _107630 _107631) = (term585 A B C P lt2 s p z _107628 t _107629 _107630 _107631).
Proof. exact (eq_refl (term597 A B C P lt2 s p z _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128651 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term585 A B C P lt2 s p z _107628 t _107629 _107630 _107631.
Proof. exact (EQ_MP (@lem8128650 A B C P lt2 s p z _107628 t _107629 _107630 _107631) (@lem8128649 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8128652 {A B P : Type'} (_107632 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term598 A B P lt2 s a f g _107632.
Proof. exact (@lem8128518 A B P p lt2 s a f g h1 _107632). Qed.
Lemma lem8128653 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107632 : A) : (term598 A B P lt2 s a f g _107632) = (term486 A B P lt2 s a f g _107632).
Proof. exact (eq_refl (term598 A B P lt2 s a f g _107632)). Qed.
Lemma lem8128655 {A B C P : Type'} (_107633 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term594 A B C P lt2 s p z t _107633.
Proof. exact (@lem8128610 A B C P p lt2 s z t h1 _107633). Qed.
Lemma lem8128656 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) : (term594 A B C P lt2 s p z t _107633) = (term591 A B C P lt2 s p z _107633 t).
Proof. exact (eq_refl (term594 A B C P lt2 s p z t _107633)). Qed.
Lemma lem8128657 {A B C P : Type'} (_107633 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term591 A B C P lt2 s p z _107633 t.
Proof. exact (EQ_MP (@lem8128656 A B C P lt2 s p z _107633 t) (@lem8128655 A B C P _107633 p lt2 s z t h1)). Qed.
Lemma lem8128658 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term595 A B C P lt2 s p z _107633 t _107634.
Proof. exact (@lem8128657 A B C P _107633 p lt2 s z t h1 _107634). Qed.
Lemma lem8128659 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) : (term595 A B C P lt2 s p z _107633 t _107634) = (term589 A B C P lt2 s p z _107633 t _107634).
Proof. exact (eq_refl (term595 A B C P lt2 s p z _107633 t _107634)). Qed.
Lemma lem8128660 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term589 A B C P lt2 s p z _107633 t _107634.
Proof. exact (EQ_MP (@lem8128659 A B C P lt2 s p z _107633 t _107634) (@lem8128658 A B C P _107633 _107634 p lt2 s z t h1)). Qed.
Lemma lem8128661 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term596 A B C P lt2 s p z _107633 t _107634 _107635.
Proof. exact (@lem8128660 A B C P _107633 _107634 p lt2 s z t h1 _107635). Qed.
Lemma lem8128662 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) : (term596 A B C P lt2 s p z _107633 t _107634 _107635) = (term587 A B C P lt2 s p z _107633 t _107634 _107635).
Proof. exact (eq_refl (term596 A B C P lt2 s p z _107633 t _107634 _107635)). Qed.
Lemma lem8128663 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term587 A B C P lt2 s p z _107633 t _107634 _107635.
Proof. exact (EQ_MP (@lem8128662 A B C P lt2 s p z _107633 t _107634 _107635) (@lem8128661 A B C P _107633 _107634 _107635 p lt2 s z t h1)). Qed.
Lemma lem8128664 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term597 A B C P lt2 s p z _107633 t _107634 _107635 _107636.
Proof. exact (@lem8128663 A B C P _107633 _107634 _107635 p lt2 s z t h1 _107636). Qed.
Lemma lem8128665 {A B C P : Type'} (lt2 : type1402 A) (s : P -> A) (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term597 A B C P lt2 s p z _107633 t _107634 _107635 _107636) = (term585 A B C P lt2 s p z _107633 t _107634 _107635 _107636).
Proof. exact (eq_refl (term597 A B C P lt2 s p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128666 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term585 A B C P lt2 s p z _107633 t _107634 _107635 _107636.
Proof. exact (EQ_MP (@lem8128665 A B C P lt2 s p z _107633 t _107634 _107635 _107636) (@lem8128664 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8128667 {A B P : Type'} (_107637 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term598 A B P lt2 s a f g _107637.
Proof. exact (@lem8128631 A B P p lt2 s a f g h1 _107637). Qed.
Lemma lem8128668 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107637 : A) : (term598 A B P lt2 s a f g _107637) = (term486 A B P lt2 s a f g _107637).
Proof. exact (eq_refl (term598 A B P lt2 s a f g _107637)). Qed.
Lemma lem8128670 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term578 A B C P lt2 s p z _107628 t _107629 _107630 _107631.
Proof. exact (proj2 (@lem8128651 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8128672 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term599 A B C P p z _107628 t _107629 _107630 _107631.
Proof. exact (proj2 (@lem8128670 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8128673 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term600 A B C P p lt2 z s _107628 t _107629 _107630 _107631.
Proof. exact (proj1 (@lem8128670 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8128677 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term582 A B C P lt2 s p z _107633 t _107634 _107635 _107636.
Proof. exact (proj1 (@lem8128666 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8128680 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term601 A B C P p z _107633 t _107634 _107635 _107636.
Proof. exact (proj2 (@lem8128677 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8128681 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term602 A B C P p lt2 z s _107633 t _107634 _107635 _107636.
Proof. exact (proj1 (@lem8128677 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8128691 {A B P : Type'} (_107632 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term486 A B P lt2 s a f g _107632.
Proof. exact (EQ_MP (@lem8128653 A B P lt2 s a f g _107632) (@lem8128652 A B P _107632 p lt2 s a f g h1)). Qed.
Lemma lem8128695 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term497 A B C P t g x a.
Proof. exact (proj2 (@lem8128408 A B C P f t g x a h1)). Qed.
Lemma lem8128703 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term600 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term603 A B C P p lt2 z s _107628 t _107629 _107630 _107631).
Proof. exact (@lem8126046 (term546 A B P p _107628 _107631) (term572 A B C P p lt2 z _107628 _107629 _107630 s _107631) (term512 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128710 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term604 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term605 A B C P p lt2 z s _107628 t _107629 _107630 _107631).
Proof. exact (@lem8126046 (term546 A B P p _107629 _107631) (term541 A B C P lt2 z _107628 _107629 _107630 s _107631) (term512 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128711 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term547 A B P p _107628 _107631) = (term547 A B P p _107628 _107631).
Proof. exact (eq_refl (term547 A B P p _107628 _107631)). Qed.
Lemma lem8128714 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term603 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8128711 A B P p _107628 _107631) (@lem8128710 A B C P p lt2 z s _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128716 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term600 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631).
Proof. exact (TRANS (@lem8128703 A B C P p lt2 z s _107628 t _107629 _107630 _107631) (@lem8128714 A B C P p lt2 z s _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128717 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631.
Proof. exact (EQ_MP (@lem8128716 A B C P p lt2 z s _107628 t _107629 _107630 _107631) (@lem8128673 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8128725 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term599 A B C P p z _107628 t _107629 _107630 _107631) = (term607 A B C P p z _107628 t _107629 _107630 _107631).
Proof. exact (@lem8126046 (term546 A B P p _107628 _107631) (term573 A B C P p z _107628 _107629 _107630 _107631) (term512 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128732 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term608 A B C P p z _107628 t _107629 _107630 _107631) = (term609 A B C P p z _107628 t _107629 _107630 _107631).
Proof. exact (@lem8126046 (term546 A B P p _107629 _107631) (term534 A B C P z _107628 _107629 _107630 _107631) (term512 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128733 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term547 A B P p _107628 _107631) = (term547 A B P p _107628 _107631).
Proof. exact (eq_refl (term547 A B P p _107628 _107631)). Qed.
Lemma lem8128736 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term607 A B C P p z _107628 t _107629 _107630 _107631) = (term610 A B C P p z _107628 t _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8128733 A B P p _107628 _107631) (@lem8128732 A B C P p z _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128738 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term599 A B C P p z _107628 t _107629 _107630 _107631) = (term610 A B C P p z _107628 t _107629 _107630 _107631).
Proof. exact (TRANS (@lem8128725 A B C P p z _107628 t _107629 _107630 _107631) (@lem8128736 A B C P p z _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8128739 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term610 A B C P p z _107628 t _107629 _107630 _107631.
Proof. exact (EQ_MP (@lem8128738 A B C P p z _107628 t _107629 _107630 _107631) (@lem8128672 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8128793 {A B P : Type'} (_107637 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term486 A B P lt2 s a f g _107637.
Proof. exact (EQ_MP (@lem8128668 A B P lt2 s a f g _107637) (@lem8128667 A B P _107637 p lt2 s a f g h1)). Qed.
Lemma lem8128795 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term497 A B C P t f x a.
Proof. exact (proj1 (@lem8128409 A B C P f t g x a h1)). Qed.
Lemma lem8128849 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term602 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term611 A B C P p lt2 z s _107633 t _107634 _107635 _107636).
Proof. exact (@lem8126046 (term546 A B P p _107633 _107636) (term572 A B C P p lt2 z _107633 _107634 _107635 s _107636) (term516 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128856 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term612 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term613 A B C P p lt2 z s _107633 t _107634 _107635 _107636).
Proof. exact (@lem8126046 (term546 A B P p _107634 _107636) (term541 A B C P lt2 z _107633 _107634 _107635 s _107636) (term516 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128857 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term547 A B P p _107633 _107636) = (term547 A B P p _107633 _107636).
Proof. exact (eq_refl (term547 A B P p _107633 _107636)). Qed.
Lemma lem8128860 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term611 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8128857 A B P p _107633 _107636) (@lem8128856 A B C P p lt2 z s _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128862 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term602 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8128849 A B C P p lt2 z s _107633 t _107634 _107635 _107636) (@lem8128860 A B C P p lt2 z s _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128863 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636.
Proof. exact (EQ_MP (@lem8128862 A B C P p lt2 z s _107633 t _107634 _107635 _107636) (@lem8128681 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8128871 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term601 A B C P p z _107633 t _107634 _107635 _107636) = (term615 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (@lem8126046 (term546 A B P p _107633 _107636) (term573 A B C P p z _107633 _107634 _107635 _107636) (term516 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128878 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term616 A B C P p z _107633 t _107634 _107635 _107636) = (term617 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (@lem8126046 (term546 A B P p _107634 _107636) (term534 A B C P z _107633 _107634 _107635 _107636) (term516 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128879 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term547 A B P p _107633 _107636) = (term547 A B P p _107633 _107636).
Proof. exact (eq_refl (term547 A B P p _107633 _107636)). Qed.
Lemma lem8128882 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term615 A B C P p z _107633 t _107634 _107635 _107636) = (term618 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8128879 A B P p _107633 _107636) (@lem8128878 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128884 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term601 A B C P p z _107633 t _107634 _107635 _107636) = (term618 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8128871 A B C P p z _107633 t _107634 _107635 _107636) (@lem8128882 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8128885 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term618 A B C P p z _107633 t _107634 _107635 _107636.
Proof. exact (EQ_MP (@lem8128884 A B C P p z _107633 t _107634 _107635 _107636) (@lem8128680 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8129090 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (proj1 (@lem8127958 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129091 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p f a.
Proof. exact (fun h0 : term546 A B P p f a => @lem8129090 A B P p lt2 s a f g h1). Qed.
Lemma lem8129093 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129094 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term619 A B P p f a) = (term489 A B P p f a).
Proof. exact (@lem8129093 (term489 A B P p f a)). Qed.
Lemma lem8129095 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (EQ_MP (@lem8129094 A B P p f a) (@lem8129091 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129097 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (proj1 (@lem8128404 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129098 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p g a.
Proof. exact (fun h0 : term546 A B P p g a => @lem8129097 A B P p lt2 s a f g h1). Qed.
Lemma lem8129100 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129101 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term619 A B P p g a) = (term489 A B P p g a).
Proof. exact (@lem8129100 (term489 A B P p g a)). Qed.
Lemma lem8129102 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (EQ_MP (@lem8129101 A B P p g a) (@lem8129098 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129104 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (proj1 (@lem8127958 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129105 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p f a.
Proof. exact (fun h0 : term546 A B P p f a => @lem8129104 A B P p lt2 s a f g h1). Qed.
Lemma lem8129107 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129108 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term619 A B P p f a) = (term489 A B P p f a).
Proof. exact (@lem8129107 (term489 A B P p f a)). Qed.
Lemma lem8129109 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (EQ_MP (@lem8129108 A B P p f a) (@lem8129105 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129111 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (proj1 (@lem8128404 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129112 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p g a.
Proof. exact (fun h0 : term546 A B P p g a => @lem8129111 A B P p lt2 s a f g h1). Qed.
Lemma lem8129114 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129115 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term619 A B P p g a) = (term489 A B P p g a).
Proof. exact (@lem8129114 (term489 A B P p g a)). Qed.
Lemma lem8129116 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (EQ_MP (@lem8129115 A B P p g a) (@lem8129112 A B P p lt2 s a f g h1)). Qed.
Lemma lem8129118 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term495 A B C P t f x a.
Proof. exact (proj1 (@lem8128408 A B C P f t g x a h1)). Qed.
Lemma lem8129119 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term621 A B C P t f x a.
Proof. exact (fun h0 : term497 A B C P t f x a => @lem8129118 A B C P f t g x a h1). Qed.
Lemma lem8129121 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129122 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term621 A B C P t f x a) = (term495 A B C P t f x a).
Proof. exact (@lem8129121 (term495 A B C P t f x a)). Qed.
Lemma lem8129123 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term495 A B C P t f x a.
Proof. exact (EQ_MP (@lem8129122 A B C P t f x a) (@lem8129119 A B C P f t g x a h1)). Qed.
Lemma lem8129126 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term497 A B C P t g x a) : term497 A B C P t g x a.
Proof. exact (h1). Qed.
Lemma lem8129127 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term497 A B C P t g x a) : term622 A B C P t g x a.
Proof. exact (fun h0 : term495 A B C P t g x a => @lem8129126 A B C P t g x a h1). Qed.
Lemma lem8129129 (p : Prop) : (term623 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8129130 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term622 A B C P t g x a) = (term497 A B C P t g x a).
Proof. exact (@lem8129129 (term495 A B C P t g x a)). Qed.
Lemma lem8129131 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term497 A B C P t g x a) : term497 A B C P t g x a.
Proof. exact (EQ_MP (@lem8129130 A B C P t g x a) (@lem8129127 A B C P t g x a h1)). Qed.
Lemma lem8129147 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129148 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term605 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term624 A B C P lt2 z s p _107628 t _107629 _107630 _107631).
Proof. exact (@lem8129147 (term541 A B C P lt2 z _107628 _107629 _107630 s _107631) (term546 A B P p _107629 _107631) (term512 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129162 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129163 {A B C P : Type'} (_107628 : A -> B) (p : type560 A B P) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term625 A B C P p _107628 t _107629 _107630 _107631) = (term626 A B C P _107628 p t _107629 _107630 _107631).
Proof. exact (@lem8129162 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107629 _107631) (term495 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129177 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8129178 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term627 A B C P p t _107629 _107630 _107631) = (term628 A B C P t _107630 p _107629 _107631).
Proof. exact (@lem8129177 (term495 A B C P t _107629 _107630 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129184 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term510 A B C P t _107628 _107630 _107631) = (term510 A B C P t _107628 _107630 _107631).
Proof. exact (eq_refl (term510 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129185 {A B C P : Type'} (_107628 : A -> B) (t : type554 A B C P) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term626 A B C P _107628 p t _107629 _107630 _107631) = (term629 A B C P _107628 t _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129184 A B C P t _107628 _107630 _107631) (@lem8129178 A B C P t _107630 p _107629 _107631)). Qed.
Lemma lem8129189 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129190 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term629 A B C P _107628 t _107630 p _107629 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129189 (term495 A B C P t _107629 _107630 _107631) (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129206 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term626 A B C P _107628 p t _107629 _107630 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129185 A B C P _107628 t _107630 p _107629 _107631) (@lem8129190 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129207 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term625 A B C P p _107628 t _107629 _107630 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129163 A B C P _107628 p t _107629 _107630 _107631) (@lem8129206 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129208 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (s : P -> A) (_107631 : P) : (term631 A B C P lt2 z _107628 _107629 _107630 s _107631) = (term631 A B C P lt2 z _107628 _107629 _107630 s _107631).
Proof. exact (eq_refl (term631 A B C P lt2 z _107628 _107629 _107630 s _107631)). Qed.
Lemma lem8129209 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term624 A B C P lt2 z s p _107628 t _107629 _107630 _107631) = (term632 A B C P lt2 z s t _107628 _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129208 A B C P lt2 z _107628 _107629 _107630 s _107631) (@lem8129207 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129220 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term605 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term632 A B C P lt2 z s t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129148 A B C P lt2 z s p _107628 t _107629 _107630 _107631) (@lem8129209 A B C P lt2 z s t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129221 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term547 A B P p _107628 _107631) = (term547 A B P p _107628 _107631).
Proof. exact (eq_refl (term547 A B P p _107628 _107631)). Qed.
Lemma lem8129222 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term633 A B C P lt2 z s t _107628 _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129221 A B P p _107628 _107631) (@lem8129220 A B C P lt2 z s t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129226 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129227 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term633 A B C P lt2 z s t _107628 _107630 p _107629 _107631) = (term634 A B C P lt2 z s t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129226 (term541 A B C P lt2 z _107628 _107629 _107630 s _107631) (term546 A B P p _107628 _107631) (term630 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129241 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129242 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term635 A B C P t _107628 _107630 p _107629 _107631) = (term636 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129241 (term495 A B C P t _107629 _107630 _107631) (term546 A B P p _107628 _107631) (term637 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129256 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129257 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term638 A B C P t _107628 _107630 p _107629 _107631) = (term639 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (@lem8129256 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107628 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129273 {A B C P : Type'} (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term514 A B C P t _107629 _107630 _107631) = (term514 A B C P t _107629 _107630 _107631).
Proof. exact (eq_refl (term514 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129274 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term636 A B C P t _107628 _107630 p _107629 _107631) = (term640 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129273 A B C P t _107629 _107630 _107631) (@lem8129257 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129285 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term635 A B C P t _107628 _107630 p _107629 _107631) = (term640 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129242 A B C P t _107628 _107630 p _107629 _107631) (@lem8129274 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129286 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (s : P -> A) (_107631 : P) : (term631 A B C P lt2 z _107628 _107629 _107630 s _107631) = (term631 A B C P lt2 z _107628 _107629 _107630 s _107631).
Proof. exact (eq_refl (term631 A B C P lt2 z _107628 _107629 _107630 s _107631)). Qed.
Lemma lem8129287 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term634 A B C P lt2 z s t _107628 _107630 p _107629 _107631) = (term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129286 A B C P lt2 z _107628 _107629 _107630 s _107631) (@lem8129285 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129298 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term633 A B C P lt2 z s t _107628 _107630 p _107629 _107631) = (term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129227 A B C P lt2 z s t _107628 _107630 p _107629 _107631) (@lem8129287 A B C P lt2 z s t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129299 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129222 A B C P lt2 z s t _107628 _107630 p _107629 _107631) (@lem8129298 A B C P lt2 z s t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8129301 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term642 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term643 A B C P lt2 z s t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129300) (@lem8129299 A B C P lt2 z s t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129325 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129326 {A B C P : Type'} (_107628 : A -> B) (p : type560 A B P) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term625 A B C P p _107628 t _107629 _107630 _107631) = (term626 A B C P _107628 p t _107629 _107630 _107631).
Proof. exact (@lem8129325 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107629 _107631) (term495 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129340 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8129341 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term627 A B C P p t _107629 _107630 _107631) = (term628 A B C P t _107630 p _107629 _107631).
Proof. exact (@lem8129340 (term495 A B C P t _107629 _107630 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129347 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term510 A B C P t _107628 _107630 _107631) = (term510 A B C P t _107628 _107630 _107631).
Proof. exact (eq_refl (term510 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129348 {A B C P : Type'} (_107628 : A -> B) (t : type554 A B C P) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term626 A B C P _107628 p t _107629 _107630 _107631) = (term629 A B C P _107628 t _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129347 A B C P t _107628 _107630 _107631) (@lem8129341 A B C P t _107630 p _107629 _107631)). Qed.
Lemma lem8129352 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129353 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term629 A B C P _107628 t _107630 p _107629 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129352 (term495 A B C P t _107629 _107630 _107631) (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129369 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term626 A B C P _107628 p t _107629 _107630 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129348 A B C P _107628 t _107630 p _107629 _107631) (@lem8129353 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129370 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term625 A B C P p _107628 t _107629 _107630 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129326 A B C P _107628 p t _107629 _107630 _107631) (@lem8129369 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129371 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term547 A B P p _107628 _107631) = (term547 A B P p _107628 _107631).
Proof. exact (eq_refl (term547 A B P p _107628 _107631)). Qed.
Lemma lem8129372 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term644 A B C P p _107628 t _107629 _107630 _107631) = (term635 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129371 A B P p _107628 _107631) (@lem8129370 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129376 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129377 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term635 A B C P t _107628 _107630 p _107629 _107631) = (term636 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129376 (term495 A B C P t _107629 _107630 _107631) (term546 A B P p _107628 _107631) (term637 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129391 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129392 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term638 A B C P t _107628 _107630 p _107629 _107631) = (term639 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (@lem8129391 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107628 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129408 {A B C P : Type'} (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term514 A B C P t _107629 _107630 _107631) = (term514 A B C P t _107629 _107630 _107631).
Proof. exact (eq_refl (term514 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129409 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term636 A B C P t _107628 _107630 p _107629 _107631) = (term640 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129408 A B C P t _107629 _107630 _107631) (@lem8129392 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129420 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term635 A B C P t _107628 _107630 p _107629 _107631) = (term640 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129377 A B C P t _107628 _107630 p _107629 _107631) (@lem8129409 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129421 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term644 A B C P p _107628 t _107629 _107630 _107631) = (term640 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129372 A B C P t _107628 _107630 p _107629 _107631) (@lem8129420 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129422 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (s : P -> A) (_107631 : P) : (term631 A B C P lt2 z _107628 _107629 _107630 s _107631) = (term631 A B C P lt2 z _107628 _107629 _107630 s _107631).
Proof. exact (eq_refl (term631 A B C P lt2 z _107628 _107629 _107630 s _107631)). Qed.
Lemma lem8129423 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631) = (term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129422 A B C P lt2 z _107628 _107629 _107630 s _107631) (@lem8129421 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129434 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : ((term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631)) = ((term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631) = (term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631)).
Proof. exact (MK_COMB (@lem8129301 A B C P lt2 z s t _107630 _107628 p _107629 _107631) (@lem8129423 A B C P lt2 z s t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8129437 (x : Prop) : (x = x) = True.
Proof. exact (@lem8129436 Prop x). Qed.
Lemma lem8129438 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : ((term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631) = (term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631)) = True.
Proof. exact (@lem8129437 (term641 A B C P lt2 z s t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129439 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : ((term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631)) = True.
Proof. exact (TRANS (@lem8129434 A B C P lt2 z s t _107630 _107628 p _107629 _107631) (@lem8129438 A B C P lt2 z s t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129440 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : True = ((term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631)).
Proof. exact (SYM (@lem8129439 A B C P lt2 z s p _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129441 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term606 A B C P p lt2 z s _107628 t _107629 _107630 _107631) = (term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631).
Proof. exact (EQ_MP (@lem8129440 A B C P lt2 z s p _107628 t _107629 _107630 _107631) (@lem0)). Qed.
Lemma lem8129442 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631.
Proof. exact (EQ_MP (@lem8129441 A B C P lt2 z s p _107628 t _107629 _107630 _107631) (@lem8128717 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8129444 (b : Prop) (a : Prop) : (a \/ b) = (term646 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8129445 {A B C P : Type'} (p : type560 A B P) (t : type554 A B C P) (lt2 : type1402 A) (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (s : P -> A) (_107631 : P) : (term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631) = (term647 A B C P p t lt2 z _107628 _107629 _107630 s _107631).
Proof. exact (@lem8129444 (term644 A B C P p _107628 t _107629 _107630 _107631) (term541 A B C P lt2 z _107628 _107629 _107630 s _107631)). Qed.
Lemma lem8129447 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8129448 {A B C P : Type'} (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term650 A B C P p _107628 t _107629 _107630 _107631) = (term651 A B C P p _107628 t _107629 _107630 _107631).
Proof. exact (@lem8129447 (term546 A B P p _107628 _107631) (term625 A B C P p _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129450 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129451 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term652 A B P p _107628 _107631) = (term489 A B P p _107628 _107631).
Proof. exact (@lem8129450 (term489 A B P p _107628 _107631)). Qed.
Lemma lem8129452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8129453 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term653 A B P p _107628 _107631) = (term490 A B P p _107628 _107631).
Proof. exact (MK_COMB (@lem8129452) (@lem8129451 A B P p _107628 _107631)). Qed.
Lemma lem8129455 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8129456 {A B C P : Type'} (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term654 A B C P p _107628 t _107629 _107630 _107631) = (term655 A B C P p _107628 t _107629 _107630 _107631).
Proof. exact (@lem8129455 (term546 A B P p _107629 _107631) (term512 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129458 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129459 {A B P : Type'} (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term652 A B P p _107629 _107631) = (term489 A B P p _107629 _107631).
Proof. exact (@lem8129458 (term489 A B P p _107629 _107631)). Qed.
Lemma lem8129460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8129461 {A B P : Type'} (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term653 A B P p _107629 _107631) = (term490 A B P p _107629 _107631).
Proof. exact (MK_COMB (@lem8129460) (@lem8129459 A B P p _107629 _107631)). Qed.
Lemma lem8129463 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8129464 {A B C P : Type'} (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term656 A B C P _107628 t _107629 _107630 _107631) = (term657 A B C P _107628 t _107629 _107630 _107631).
Proof. exact (@lem8129463 (term497 A B C P t _107628 _107630 _107631) (term495 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129466 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129467 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term658 A B C P t _107628 _107630 _107631) = (term495 A B C P t _107628 _107630 _107631).
Proof. exact (@lem8129466 (term495 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8129469 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term659 A B C P t _107628 _107630 _107631) = (term503 A B C P t _107628 _107630 _107631).
Proof. exact (MK_COMB (@lem8129468) (@lem8129467 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129470 {A B C P : Type'} (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term497 A B C P t _107629 _107630 _107631) = (term497 A B C P t _107629 _107630 _107631).
Proof. exact (eq_refl (term497 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129471 {A B C P : Type'} (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term657 A B C P _107628 t _107629 _107630 _107631) = (term505 A B C P _107628 t _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8129469 A B C P t _107628 _107630 _107631) (@lem8129470 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129472 {A B C P : Type'} (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term656 A B C P _107628 t _107629 _107630 _107631) = (term505 A B C P _107628 t _107629 _107630 _107631).
Proof. exact (TRANS (@lem8129464 A B C P _107628 t _107629 _107630 _107631) (@lem8129471 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129473 {A B C P : Type'} (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term655 A B C P p _107628 t _107629 _107630 _107631) = (term660 A B C P p _107628 t _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8129461 A B P p _107629 _107631) (@lem8129472 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129474 {A B C P : Type'} (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term654 A B C P p _107628 t _107629 _107630 _107631) = (term660 A B C P p _107628 t _107629 _107630 _107631).
Proof. exact (TRANS (@lem8129456 A B C P p _107628 t _107629 _107630 _107631) (@lem8129473 A B C P p _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129475 {A B C P : Type'} (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term651 A B C P p _107628 t _107629 _107630 _107631) = (term661 A B C P p _107628 t _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8129453 A B P p _107628 _107631) (@lem8129474 A B C P p _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129476 {A B C P : Type'} (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term650 A B C P p _107628 t _107629 _107630 _107631) = (term661 A B C P p _107628 t _107629 _107630 _107631).
Proof. exact (TRANS (@lem8129448 A B C P p _107628 t _107629 _107630 _107631) (@lem8129475 A B C P p _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8129478 {A B C P : Type'} (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term662 A B C P p _107628 t _107629 _107630 _107631) = (term663 A B C P p _107628 t _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8129477) (@lem8129476 A B C P p _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129479 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (s : P -> A) (_107631 : P) : (term541 A B C P lt2 z _107628 _107629 _107630 s _107631) = (term541 A B C P lt2 z _107628 _107629 _107630 s _107631).
Proof. exact (eq_refl (term541 A B C P lt2 z _107628 _107629 _107630 s _107631)). Qed.
Lemma lem8129480 {A B C P : Type'} (p : type560 A B P) (t : type554 A B C P) (lt2 : type1402 A) (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (s : P -> A) (_107631 : P) : (term647 A B C P p t lt2 z _107628 _107629 _107630 s _107631) = (term664 A B C P p t lt2 z _107628 _107629 _107630 s _107631).
Proof. exact (MK_COMB (@lem8129478 A B C P p _107628 t _107629 _107630 _107631) (@lem8129479 A B C P lt2 z _107628 _107629 _107630 s _107631)). Qed.
Lemma lem8129481 {A B C P : Type'} (p : type560 A B P) (t : type554 A B C P) (lt2 : type1402 A) (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (s : P -> A) (_107631 : P) : (term645 A B C P lt2 z s p _107628 t _107629 _107630 _107631) = (term664 A B C P p t lt2 z _107628 _107629 _107630 s _107631).
Proof. exact (TRANS (@lem8129445 A B C P p t lt2 z _107628 _107629 _107630 s _107631) (@lem8129480 A B C P p t lt2 z _107628 _107629 _107630 s _107631)). Qed.
Lemma lem8129483 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term497 A B C P t g x a) (h2 : term505 A B C P f t g x a) : term505 A B C P f t g x a.
Proof. exact (conj (@lem8129123 A B C P f t g x a h2) (@lem8129131 A B C P t g x a h1)). Qed.
Lemma lem8129484 {A B C P : Type'} (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term497 A B C P t g x a) (h2 : term505 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term660 A B C P p f t g x a.
Proof. exact (conj (@lem8129116 A B P p lt2 s a f g h3) (@lem8129483 A B C P f t g x a h1 h2)). Qed.
Lemma lem8129485 {A B C P : Type'} (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term497 A B C P t g x a) (h2 : term505 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term661 A B C P p f t g x a.
Proof. exact (conj (@lem8129109 A B P p lt2 s a f g h3) (@lem8129484 A B C P t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8129487 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term664 A B C P p t lt2 z _107628 _107629 _107630 s _107631.
Proof. exact (EQ_MP (@lem8129481 A B C P p t lt2 z _107628 _107629 _107630 s _107631) (@lem8129442 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8129488 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term664 A B C P p t lt2 z _107628 _107629 _107630 s _107631.
Proof. exact (@lem8129487 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1). Qed.
Lemma lem8129489 {A B C P : Type'} (f : A -> B) (g : A -> B) (x : C) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term664 A B C P p t lt2 z f g x s a.
Proof. exact (@lem8129488 A B C P f g x a p lt2 s z t h1). Qed.
Lemma lem8129492 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term541 A B C P lt2 z f g x s a.
Proof. exact (@lem8129489 A B C P f g x a p lt2 s z t h1 (@lem8129485 A B C P t x p lt2 s a f g h2 h3 h4)). Qed.
Lemma lem8129493 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term665 A B C P lt2 z f g x s a.
Proof. exact (fun h0 : term666 A B C P lt2 z f g x s a => @lem8129492 A B C P z t x p lt2 s a f g h1 h2 h3 h4). Qed.
Lemma lem8129495 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129496 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (x : C) (s : P -> A) (a : P) : (term665 A B C P lt2 z f g x s a) = (term541 A B C P lt2 z f g x s a).
Proof. exact (@lem8129495 (term541 A B C P lt2 z f g x s a)). Qed.
Lemma lem8129497 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term541 A B C P lt2 z f g x s a.
Proof. exact (EQ_MP (@lem8129496 A B C P lt2 z f g x s a) (@lem8129493 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8129503 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8129504 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : (term486 A B P lt2 s a f g _107632) = (term667 A B P f g lt2 _107632 s a).
Proof. exact (@lem8129503 ((@I (A -> B) f _107632) = (@I (A -> B) g _107632)) (term483 A P lt2 _107632 s a)). Qed.
Lemma lem8129512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8129513 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : (term668 A B P lt2 s a f g _107632) = (term669 A B P f g lt2 _107632 s a).
Proof. exact (MK_COMB (@lem8129512) (@lem8129504 A B P f g lt2 _107632 s a)). Qed.
Lemma lem8129521 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : (term667 A B P f g lt2 _107632 s a) = (term667 A B P f g lt2 _107632 s a).
Proof. exact (eq_refl (term667 A B P f g lt2 _107632 s a)). Qed.
Lemma lem8129522 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : ((term486 A B P lt2 s a f g _107632) = (term667 A B P f g lt2 _107632 s a)) = ((term667 A B P f g lt2 _107632 s a) = (term667 A B P f g lt2 _107632 s a)).
Proof. exact (MK_COMB (@lem8129513 A B P f g lt2 _107632 s a) (@lem8129521 A B P f g lt2 _107632 s a)). Qed.
Lemma lem8129524 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8129525 (x : Prop) : (x = x) = True.
Proof. exact (@lem8129524 Prop x). Qed.
Lemma lem8129526 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : ((term667 A B P f g lt2 _107632 s a) = (term667 A B P f g lt2 _107632 s a)) = True.
Proof. exact (@lem8129525 (term667 A B P f g lt2 _107632 s a)). Qed.
Lemma lem8129527 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : ((term486 A B P lt2 s a f g _107632) = (term667 A B P f g lt2 _107632 s a)) = True.
Proof. exact (TRANS (@lem8129522 A B P f g lt2 _107632 s a) (@lem8129526 A B P f g lt2 _107632 s a)). Qed.
Lemma lem8129528 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : True = ((term486 A B P lt2 s a f g _107632) = (term667 A B P f g lt2 _107632 s a)).
Proof. exact (SYM (@lem8129527 A B P f g lt2 _107632 s a)). Qed.
Lemma lem8129529 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : (term486 A B P lt2 s a f g _107632) = (term667 A B P f g lt2 _107632 s a).
Proof. exact (EQ_MP (@lem8129528 A B P f g lt2 _107632 s a) (@lem0)). Qed.
Lemma lem8129530 {A B P : Type'} (_107632 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term667 A B P f g lt2 _107632 s a.
Proof. exact (EQ_MP (@lem8129529 A B P f g lt2 _107632 s a) (@lem8128691 A B P _107632 p lt2 s a f g h1)). Qed.
Lemma lem8129532 (b : Prop) (a : Prop) : (a \/ b) = (term646 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8129533 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107632 : A) : (term667 A B P f g lt2 _107632 s a) = (term670 A B P lt2 s a f g _107632).
Proof. exact (@lem8129532 (term483 A P lt2 _107632 s a) ((@I (A -> B) f _107632) = (@I (A -> B) g _107632))). Qed.
Lemma lem8129535 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129536 {A P : Type'} (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : (term671 A P lt2 _107632 s a) = (term481 A P lt2 _107632 s a).
Proof. exact (@lem8129535 (term481 A P lt2 _107632 s a)). Qed.
Lemma lem8129537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8129538 {A P : Type'} (lt2 : type1402 A) (_107632 : A) (s : P -> A) (a : P) : (term672 A P lt2 _107632 s a) = (term673 A P lt2 _107632 s a).
Proof. exact (MK_COMB (@lem8129537) (@lem8129536 A P lt2 _107632 s a)). Qed.
Lemma lem8129539 {A B : Type'} (f : A -> B) (g : A -> B) (_107632 : A) : ((@I (A -> B) f _107632) = (@I (A -> B) g _107632)) = ((@I (A -> B) f _107632) = (@I (A -> B) g _107632)).
Proof. exact (eq_refl ((@I (A -> B) f _107632) = (@I (A -> B) g _107632))). Qed.
Lemma lem8129540 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107632 : A) : (term670 A B P lt2 s a f g _107632) = (term674 A B P lt2 s a f g _107632).
Proof. exact (MK_COMB (@lem8129538 A P lt2 _107632 s a) (@lem8129539 A B f g _107632)). Qed.
Lemma lem8129541 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107632 : A) : (term667 A B P f g lt2 _107632 s a) = (term674 A B P lt2 s a f g _107632).
Proof. exact (TRANS (@lem8129533 A B P lt2 s a f g _107632) (@lem8129540 A B P lt2 s a f g _107632)). Qed.
Lemma lem8129544 {A B P : Type'} (_107632 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term674 A B P lt2 s a f g _107632.
Proof. exact (EQ_MP (@lem8129541 A B P lt2 s a f g _107632) (@lem8129530 A B P _107632 p lt2 s a f g h1)). Qed.
Lemma lem8129545 {A B P : Type'} (_107632 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term674 A B P lt2 s a f g _107632.
Proof. exact (@lem8129544 A B P _107632 p lt2 s a f g h1). Qed.
Lemma lem8129546 {A B C P : Type'} (z : type517 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term675 A B C P lt2 s z f g x a.
Proof. exact (@lem8129545 A B P (term524 A B C P z f g x a) p lt2 s a f g h1). Qed.
Lemma lem8129549 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : (term527 A B C P z f g x a) = (term530 A B C P z f g x a).
Proof. exact (@lem8129546 A B C P z x p lt2 s a f g h4 (@lem8129497 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8129550 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term676 A B C P z f g x a.
Proof. exact (fun h0 : term534 A B C P z f g x a => @lem8129549 A B C P z t x p lt2 s a f g h1 h2 h3 h4). Qed.
Lemma lem8129552 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129553 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (x : C) (a : P) : (term676 A B C P z f g x a) = ((term527 A B C P z f g x a) = (term530 A B C P z f g x a)).
Proof. exact (@lem8129552 ((term527 A B C P z f g x a) = (term530 A B C P z f g x a))). Qed.
Lemma lem8129554 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : (term527 A B C P z f g x a) = (term530 A B C P z f g x a).
Proof. exact (EQ_MP (@lem8129553 A B C P z f g x a) (@lem8129550 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8129556 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term495 A B C P t f x a.
Proof. exact (proj1 (@lem8128408 A B C P f t g x a h1)). Qed.
Lemma lem8129557 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term621 A B C P t f x a.
Proof. exact (fun h0 : term497 A B C P t f x a => @lem8129556 A B C P f t g x a h1). Qed.
Lemma lem8129559 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129560 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term621 A B C P t f x a) = (term495 A B C P t f x a).
Proof. exact (@lem8129559 (term495 A B C P t f x a)). Qed.
Lemma lem8129561 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term495 A B C P t f x a.
Proof. exact (EQ_MP (@lem8129560 A B C P t f x a) (@lem8129557 A B C P f t g x a h1)). Qed.
Lemma lem8129577 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129578 {A B C P : Type'} (z : type517 A B C P) (p : type560 A B P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term609 A B C P p z _107628 t _107629 _107630 _107631) = (term677 A B C P z p _107628 t _107629 _107630 _107631).
Proof. exact (@lem8129577 (term534 A B C P z _107628 _107629 _107630 _107631) (term546 A B P p _107629 _107631) (term512 A B C P _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129594 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129595 {A B C P : Type'} (_107628 : A -> B) (p : type560 A B P) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term625 A B C P p _107628 t _107629 _107630 _107631) = (term626 A B C P _107628 p t _107629 _107630 _107631).
Proof. exact (@lem8129594 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107629 _107631) (term495 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129609 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8129610 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term627 A B C P p t _107629 _107630 _107631) = (term628 A B C P t _107630 p _107629 _107631).
Proof. exact (@lem8129609 (term495 A B C P t _107629 _107630 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129616 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term510 A B C P t _107628 _107630 _107631) = (term510 A B C P t _107628 _107630 _107631).
Proof. exact (eq_refl (term510 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129617 {A B C P : Type'} (_107628 : A -> B) (t : type554 A B C P) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term626 A B C P _107628 p t _107629 _107630 _107631) = (term629 A B C P _107628 t _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129616 A B C P t _107628 _107630 _107631) (@lem8129610 A B C P t _107630 p _107629 _107631)). Qed.
Lemma lem8129621 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129622 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term629 A B C P _107628 t _107630 p _107629 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129621 (term495 A B C P t _107629 _107630 _107631) (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129638 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term626 A B C P _107628 p t _107629 _107630 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129617 A B C P _107628 t _107630 p _107629 _107631) (@lem8129622 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129639 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term625 A B C P p _107628 t _107629 _107630 _107631) = (term630 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129595 A B C P _107628 p t _107629 _107630 _107631) (@lem8129638 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129640 {A B C P : Type'} (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term678 A B C P z _107628 _107629 _107630 _107631) = (term678 A B C P z _107628 _107629 _107630 _107631).
Proof. exact (eq_refl (term678 A B C P z _107628 _107629 _107630 _107631)). Qed.
Lemma lem8129641 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term677 A B C P z p _107628 t _107629 _107630 _107631) = (term679 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129640 A B C P z _107628 _107629 _107630 _107631) (@lem8129639 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129645 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129646 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term679 A B C P z t _107628 _107630 p _107629 _107631) = (term680 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129645 (term495 A B C P t _107629 _107630 _107631) (term534 A B C P z _107628 _107629 _107630 _107631) (term637 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129674 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term677 A B C P z p _107628 t _107629 _107630 _107631) = (term680 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129641 A B C P z t _107628 _107630 p _107629 _107631) (@lem8129646 A B C P z t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129675 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term609 A B C P p z _107628 t _107629 _107630 _107631) = (term680 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129578 A B C P z p _107628 t _107629 _107630 _107631) (@lem8129674 A B C P z t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129676 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term547 A B P p _107628 _107631) = (term547 A B P p _107628 _107631).
Proof. exact (eq_refl (term547 A B P p _107628 _107631)). Qed.
Lemma lem8129677 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term610 A B C P p z _107628 t _107629 _107630 _107631) = (term681 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129676 A B P p _107628 _107631) (@lem8129675 A B C P z t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129681 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129682 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term681 A B C P z t _107628 _107630 p _107629 _107631) = (term682 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129681 (term495 A B C P t _107629 _107630 _107631) (term546 A B P p _107628 _107631) (term683 A B C P z t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129696 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129697 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term684 A B C P z t _107628 _107630 p _107629 _107631) = (term685 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129696 (term534 A B C P z _107628 _107629 _107630 _107631) (term546 A B P p _107628 _107631) (term637 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129713 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129714 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term638 A B C P t _107628 _107630 p _107629 _107631) = (term639 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (@lem8129713 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107628 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129730 {A B C P : Type'} (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term678 A B C P z _107628 _107629 _107630 _107631) = (term678 A B C P z _107628 _107629 _107630 _107631).
Proof. exact (eq_refl (term678 A B C P z _107628 _107629 _107630 _107631)). Qed.
Lemma lem8129731 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term685 A B C P z t _107628 _107630 p _107629 _107631) = (term686 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129730 A B C P z _107628 _107629 _107630 _107631) (@lem8129714 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129742 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term684 A B C P z t _107628 _107630 p _107629 _107631) = (term686 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129697 A B C P z t _107628 _107630 p _107629 _107631) (@lem8129731 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129743 {A B C P : Type'} (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term514 A B C P t _107629 _107630 _107631) = (term514 A B C P t _107629 _107630 _107631).
Proof. exact (eq_refl (term514 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129744 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term682 A B C P z t _107628 _107630 p _107629 _107631) = (term687 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129743 A B C P t _107629 _107630 _107631) (@lem8129742 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129755 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term681 A B C P z t _107628 _107630 p _107629 _107631) = (term687 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129682 A B C P z t _107628 _107630 p _107629 _107631) (@lem8129744 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129756 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term610 A B C P p z _107628 t _107629 _107630 _107631) = (term687 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129677 A B C P z t _107628 _107630 p _107629 _107631) (@lem8129755 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8129758 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term688 A B C P p z _107628 t _107629 _107630 _107631) = (term689 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129757) (@lem8129756 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129782 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129783 {A B C P : Type'} (z : type517 A B C P) (p : type560 A B P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term690 A B C P p z _107629 t _107628 _107630 _107631) = (term691 A B C P z p _107629 t _107628 _107630 _107631).
Proof. exact (@lem8129782 (term534 A B C P z _107628 _107629 _107630 _107631) (term546 A B P p _107629 _107631) (term497 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129799 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8129800 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term692 A B C P p _107629 t _107628 _107630 _107631) = (term637 A B C P t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129799 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129806 {A B C P : Type'} (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term678 A B C P z _107628 _107629 _107630 _107631) = (term678 A B C P z _107628 _107629 _107630 _107631).
Proof. exact (eq_refl (term678 A B C P z _107628 _107629 _107630 _107631)). Qed.
Lemma lem8129807 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term691 A B C P z p _107629 t _107628 _107630 _107631) = (term683 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129806 A B C P z _107628 _107629 _107630 _107631) (@lem8129800 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129818 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term690 A B C P p z _107629 t _107628 _107630 _107631) = (term683 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (TRANS (@lem8129783 A B C P z p _107629 t _107628 _107630 _107631) (@lem8129807 A B C P z t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129819 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term547 A B P p _107628 _107631) = (term547 A B P p _107628 _107631).
Proof. exact (eq_refl (term547 A B P p _107628 _107631)). Qed.
Lemma lem8129820 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term693 A B C P p z _107629 t _107628 _107630 _107631) = (term684 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129819 A B P p _107628 _107631) (@lem8129818 A B C P z t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129824 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129825 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term684 A B C P z t _107628 _107630 p _107629 _107631) = (term685 A B C P z t _107628 _107630 p _107629 _107631).
Proof. exact (@lem8129824 (term534 A B C P z _107628 _107629 _107630 _107631) (term546 A B P p _107628 _107631) (term637 A B C P t _107628 _107630 p _107629 _107631)). Qed.
Lemma lem8129841 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8129842 {A B C P : Type'} (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term638 A B C P t _107628 _107630 p _107629 _107631) = (term639 A B C P t _107630 _107628 p _107629 _107631).
Proof. exact (@lem8129841 (term497 A B C P t _107628 _107630 _107631) (term546 A B P p _107628 _107631) (term546 A B P p _107629 _107631)). Qed.
Lemma lem8129858 {A B C P : Type'} (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term678 A B C P z _107628 _107629 _107630 _107631) = (term678 A B C P z _107628 _107629 _107630 _107631).
Proof. exact (eq_refl (term678 A B C P z _107628 _107629 _107630 _107631)). Qed.
Lemma lem8129859 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term685 A B C P z t _107628 _107630 p _107629 _107631) = (term686 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129858 A B C P z _107628 _107629 _107630 _107631) (@lem8129842 A B C P t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129870 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term684 A B C P z t _107628 _107630 p _107629 _107631) = (term686 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129825 A B C P z t _107628 _107630 p _107629 _107631) (@lem8129859 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129871 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term693 A B C P p z _107629 t _107628 _107630 _107631) = (term686 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (TRANS (@lem8129820 A B C P z t _107628 _107630 p _107629 _107631) (@lem8129870 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129872 {A B C P : Type'} (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term514 A B C P t _107629 _107630 _107631) = (term514 A B C P t _107629 _107630 _107631).
Proof. exact (eq_refl (term514 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129873 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term694 A B C P p z _107629 t _107628 _107630 _107631) = (term687 A B C P z t _107630 _107628 p _107629 _107631).
Proof. exact (MK_COMB (@lem8129872 A B C P t _107629 _107630 _107631) (@lem8129871 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129884 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : ((term610 A B C P p z _107628 t _107629 _107630 _107631) = (term694 A B C P p z _107629 t _107628 _107630 _107631)) = ((term687 A B C P z t _107630 _107628 p _107629 _107631) = (term687 A B C P z t _107630 _107628 p _107629 _107631)).
Proof. exact (MK_COMB (@lem8129758 A B C P z t _107630 _107628 p _107629 _107631) (@lem8129873 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129886 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8129887 (x : Prop) : (x = x) = True.
Proof. exact (@lem8129886 Prop x). Qed.
Lemma lem8129888 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107630 : C) (_107628 : A -> B) (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : ((term687 A B C P z t _107630 _107628 p _107629 _107631) = (term687 A B C P z t _107630 _107628 p _107629 _107631)) = True.
Proof. exact (@lem8129887 (term687 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129889 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : ((term610 A B C P p z _107628 t _107629 _107630 _107631) = (term694 A B C P p z _107629 t _107628 _107630 _107631)) = True.
Proof. exact (TRANS (@lem8129884 A B C P z t _107630 _107628 p _107629 _107631) (@lem8129888 A B C P z t _107630 _107628 p _107629 _107631)). Qed.
Lemma lem8129890 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : True = ((term610 A B C P p z _107628 t _107629 _107630 _107631) = (term694 A B C P p z _107629 t _107628 _107630 _107631)).
Proof. exact (SYM (@lem8129889 A B C P p z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129891 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term610 A B C P p z _107628 t _107629 _107630 _107631) = (term694 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (EQ_MP (@lem8129890 A B C P p z _107629 t _107628 _107630 _107631) (@lem0)). Qed.
Lemma lem8129892 {A B C P : Type'} (_107629 : A -> B) (_107628 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term694 A B C P p z _107629 t _107628 _107630 _107631.
Proof. exact (EQ_MP (@lem8129891 A B C P p z _107629 t _107628 _107630 _107631) (@lem8128739 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8129894 (b : Prop) (a : Prop) : (a \/ b) = (term646 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8129895 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term694 A B C P p z _107629 t _107628 _107630 _107631) = (term695 A B C P p z _107628 t _107629 _107630 _107631).
Proof. exact (@lem8129894 (term693 A B C P p z _107629 t _107628 _107630 _107631) (term495 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129897 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8129898 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term696 A B C P p z _107629 t _107628 _107630 _107631) = (term697 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (@lem8129897 (term546 A B P p _107628 _107631) (term690 A B C P p z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129900 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129901 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term652 A B P p _107628 _107631) = (term489 A B P p _107628 _107631).
Proof. exact (@lem8129900 (term489 A B P p _107628 _107631)). Qed.
Lemma lem8129902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8129903 {A B P : Type'} (p : type560 A B P) (_107628 : A -> B) (_107631 : P) : (term653 A B P p _107628 _107631) = (term490 A B P p _107628 _107631).
Proof. exact (MK_COMB (@lem8129902) (@lem8129901 A B P p _107628 _107631)). Qed.
Lemma lem8129905 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8129906 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term698 A B C P p z _107629 t _107628 _107630 _107631) = (term699 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (@lem8129905 (term546 A B P p _107629 _107631) (term700 A B C P z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129908 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129909 {A B P : Type'} (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term652 A B P p _107629 _107631) = (term489 A B P p _107629 _107631).
Proof. exact (@lem8129908 (term489 A B P p _107629 _107631)). Qed.
Lemma lem8129910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8129911 {A B P : Type'} (p : type560 A B P) (_107629 : A -> B) (_107631 : P) : (term653 A B P p _107629 _107631) = (term490 A B P p _107629 _107631).
Proof. exact (MK_COMB (@lem8129910) (@lem8129909 A B P p _107629 _107631)). Qed.
Lemma lem8129913 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8129914 {A B C P : Type'} (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term701 A B C P z _107629 t _107628 _107630 _107631) = (term702 A B C P z _107629 t _107628 _107630 _107631).
Proof. exact (@lem8129913 (term534 A B C P z _107628 _107629 _107630 _107631) (term497 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129916 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129917 {A B C P : Type'} (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term703 A B C P z _107628 _107629 _107630 _107631) = ((term527 A B C P z _107628 _107629 _107630 _107631) = (term530 A B C P z _107628 _107629 _107630 _107631)).
Proof. exact (@lem8129916 ((term527 A B C P z _107628 _107629 _107630 _107631) = (term530 A B C P z _107628 _107629 _107630 _107631))). Qed.
Lemma lem8129918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8129919 {A B C P : Type'} (z : type517 A B C P) (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term704 A B C P z _107628 _107629 _107630 _107631) = (term705 A B C P z _107628 _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8129918) (@lem8129917 A B C P z _107628 _107629 _107630 _107631)). Qed.
Lemma lem8129921 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8129922 {A B C P : Type'} (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term658 A B C P t _107628 _107630 _107631) = (term495 A B C P t _107628 _107630 _107631).
Proof. exact (@lem8129921 (term495 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129923 {A B C P : Type'} (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term702 A B C P z _107629 t _107628 _107630 _107631) = (term706 A B C P z _107629 t _107628 _107630 _107631).
Proof. exact (MK_COMB (@lem8129919 A B C P z _107628 _107629 _107630 _107631) (@lem8129922 A B C P t _107628 _107630 _107631)). Qed.
Lemma lem8129924 {A B C P : Type'} (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term701 A B C P z _107629 t _107628 _107630 _107631) = (term706 A B C P z _107629 t _107628 _107630 _107631).
Proof. exact (TRANS (@lem8129914 A B C P z _107629 t _107628 _107630 _107631) (@lem8129923 A B C P z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129925 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term699 A B C P p z _107629 t _107628 _107630 _107631) = (term707 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (MK_COMB (@lem8129911 A B P p _107629 _107631) (@lem8129924 A B C P z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129926 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term698 A B C P p z _107629 t _107628 _107630 _107631) = (term707 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (TRANS (@lem8129906 A B C P p z _107629 t _107628 _107630 _107631) (@lem8129925 A B C P p z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129927 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term697 A B C P p z _107629 t _107628 _107630 _107631) = (term708 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (MK_COMB (@lem8129903 A B P p _107628 _107631) (@lem8129926 A B C P p z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129928 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term696 A B C P p z _107629 t _107628 _107630 _107631) = (term708 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (TRANS (@lem8129898 A B C P p z _107629 t _107628 _107630 _107631) (@lem8129927 A B C P p z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129929 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8129930 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107629 : A -> B) (t : type554 A B C P) (_107628 : A -> B) (_107630 : C) (_107631 : P) : (term709 A B C P p z _107629 t _107628 _107630 _107631) = (term710 A B C P p z _107629 t _107628 _107630 _107631).
Proof. exact (MK_COMB (@lem8129929) (@lem8129928 A B C P p z _107629 t _107628 _107630 _107631)). Qed.
Lemma lem8129931 {A B C P : Type'} (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term495 A B C P t _107629 _107630 _107631) = (term495 A B C P t _107629 _107630 _107631).
Proof. exact (eq_refl (term495 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129932 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term695 A B C P p z _107628 t _107629 _107630 _107631) = (term711 A B C P p z _107628 t _107629 _107630 _107631).
Proof. exact (MK_COMB (@lem8129930 A B C P p z _107629 t _107628 _107630 _107631) (@lem8129931 A B C P t _107629 _107630 _107631)). Qed.
Lemma lem8129933 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107628 : A -> B) (t : type554 A B C P) (_107629 : A -> B) (_107630 : C) (_107631 : P) : (term694 A B C P p z _107629 t _107628 _107630 _107631) = (term711 A B C P p z _107628 t _107629 _107630 _107631).
Proof. exact (TRANS (@lem8129895 A B C P p z _107628 t _107629 _107630 _107631) (@lem8129932 A B C P p z _107628 t _107629 _107630 _107631)). Qed.
Lemma lem8129935 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term706 A B C P z g t f x a.
Proof. exact (conj (@lem8129554 A B C P z t x p lt2 s a f g h1 h2 h3 h4) (@lem8129561 A B C P f t g x a h3)). Qed.
Lemma lem8129936 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term707 A B C P p z g t f x a.
Proof. exact (conj (@lem8129102 A B P p lt2 s a f g h4) (@lem8129935 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8129937 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term708 A B C P p z g t f x a.
Proof. exact (conj (@lem8129095 A B P p lt2 s a f g h4) (@lem8129936 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8129939 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term711 A B C P p z _107628 t _107629 _107630 _107631.
Proof. exact (EQ_MP (@lem8129933 A B C P p z _107628 t _107629 _107630 _107631) (@lem8129892 A B C P _107629 _107628 _107630 _107631 p lt2 s z t h1)). Qed.
Lemma lem8129940 {A B C P : Type'} (_107628 : A -> B) (_107629 : A -> B) (_107630 : C) (_107631 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term711 A B C P p z _107628 t _107629 _107630 _107631.
Proof. exact (@lem8129939 A B C P _107628 _107629 _107630 _107631 p lt2 s z t h1). Qed.
Lemma lem8129941 {A B C P : Type'} (f : A -> B) (g : A -> B) (x : C) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term711 A B C P p z f t g x a.
Proof. exact (@lem8129940 A B C P f g x a p lt2 s z t h1). Qed.
Lemma lem8129944 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t g x a) (h3 : term505 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term495 A B C P t g x a.
Proof. exact (@lem8129941 A B C P f g x a p lt2 s z t h1 (@lem8129937 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8129945 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term505 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term621 A B C P t g x a.
Proof. exact (fun h0 : term497 A B C P t g x a => @lem8129944 A B C P z t x p lt2 s a f g h1 h0 h2 h3). Qed.
Lemma lem8129947 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129948 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term621 A B C P t g x a) = (term495 A B C P t g x a).
Proof. exact (@lem8129947 (term495 A B C P t g x a)). Qed.
Lemma lem8129949 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term505 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term495 A B C P t g x a.
Proof. exact (EQ_MP (@lem8129948 A B C P t g x a) (@lem8129945 A B C P z t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8129952 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8129954 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term497 A B C P t g x a) = (term712 A B C P t g x a).
Proof. exact (@lem8129952 (term495 A B C P t g x a)). Qed.
Lemma lem8129957 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term505 A B C P f t g x a) : term712 A B C P t g x a.
Proof. exact (EQ_MP (@lem8129954 A B C P t g x a) (@lem8128695 A B C P f t g x a h1)). Qed.
Lemma lem8129960 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term505 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : False.
Proof. exact (@lem8129957 A B C P f t g x a h2 (@lem8129949 A B C P z t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8129961 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term505 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term713.
Proof. exact (fun h0 : ~ False => @lem8129960 A B C P z t x p lt2 s a f g h1 h2 h3). Qed.
Lemma lem8129963 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8129964 : term713 = False.
Proof. exact (@lem8129963 False). Qed.
Lemma lem8129965 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term505 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8129964) (@lem8129961 A B C P z t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8130170 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (proj1 (@lem8127958 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130171 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p f a.
Proof. exact (fun h0 : term546 A B P p f a => @lem8130170 A B P p lt2 s a f g h1). Qed.
Lemma lem8130173 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130174 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term619 A B P p f a) = (term489 A B P p f a).
Proof. exact (@lem8130173 (term489 A B P p f a)). Qed.
Lemma lem8130175 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (EQ_MP (@lem8130174 A B P p f a) (@lem8130171 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130177 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (proj1 (@lem8128404 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130178 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p g a.
Proof. exact (fun h0 : term546 A B P p g a => @lem8130177 A B P p lt2 s a f g h1). Qed.
Lemma lem8130180 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130181 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term619 A B P p g a) = (term489 A B P p g a).
Proof. exact (@lem8130180 (term489 A B P p g a)). Qed.
Lemma lem8130182 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (EQ_MP (@lem8130181 A B P p g a) (@lem8130178 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130184 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (proj1 (@lem8127958 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130185 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p f a.
Proof. exact (fun h0 : term546 A B P p f a => @lem8130184 A B P p lt2 s a f g h1). Qed.
Lemma lem8130187 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130188 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term619 A B P p f a) = (term489 A B P p f a).
Proof. exact (@lem8130187 (term489 A B P p f a)). Qed.
Lemma lem8130189 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p f a.
Proof. exact (EQ_MP (@lem8130188 A B P p f a) (@lem8130185 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130191 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (proj1 (@lem8128404 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130192 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term619 A B P p g a.
Proof. exact (fun h0 : term546 A B P p g a => @lem8130191 A B P p lt2 s a f g h1). Qed.
Lemma lem8130194 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130195 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term619 A B P p g a) = (term489 A B P p g a).
Proof. exact (@lem8130194 (term489 A B P p g a)). Qed.
Lemma lem8130196 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term489 A B P p g a.
Proof. exact (EQ_MP (@lem8130195 A B P p g a) (@lem8130192 A B P p lt2 s a f g h1)). Qed.
Lemma lem8130199 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) (h1 : term497 A B C P t f x a) : term497 A B C P t f x a.
Proof. exact (h1). Qed.
Lemma lem8130200 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) (h1 : term497 A B C P t f x a) : term622 A B C P t f x a.
Proof. exact (fun h0 : term495 A B C P t f x a => @lem8130199 A B C P t f x a h1). Qed.
Lemma lem8130202 (p : Prop) : (term623 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8130203 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term622 A B C P t f x a) = (term497 A B C P t f x a).
Proof. exact (@lem8130202 (term495 A B C P t f x a)). Qed.
Lemma lem8130204 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) (h1 : term497 A B C P t f x a) : term497 A B C P t f x a.
Proof. exact (EQ_MP (@lem8130203 A B C P t f x a) (@lem8130200 A B C P t f x a h1)). Qed.
Lemma lem8130206 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term495 A B C P t g x a.
Proof. exact (proj2 (@lem8128409 A B C P f t g x a h1)). Qed.
Lemma lem8130207 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term621 A B C P t g x a.
Proof. exact (fun h0 : term497 A B C P t g x a => @lem8130206 A B C P f t g x a h1). Qed.
Lemma lem8130209 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130210 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term621 A B C P t g x a) = (term495 A B C P t g x a).
Proof. exact (@lem8130209 (term495 A B C P t g x a)). Qed.
Lemma lem8130211 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term495 A B C P t g x a.
Proof. exact (EQ_MP (@lem8130210 A B C P t g x a) (@lem8130207 A B C P f t g x a h1)). Qed.
Lemma lem8130227 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130228 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term613 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term714 A B C P lt2 z s p _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130227 (term541 A B C P lt2 z _107633 _107634 _107635 s _107636) (term546 A B P p _107634 _107636) (term516 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130242 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130243 {A B C P : Type'} (_107633 : A -> B) (p : type560 A B P) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term715 A B C P p _107633 t _107634 _107635 _107636) = (term716 A B C P _107633 p t _107634 _107635 _107636).
Proof. exact (@lem8130242 (term495 A B C P t _107633 _107635 _107636) (term546 A B P p _107634 _107636) (term497 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130257 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8130258 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term717 A B C P p t _107634 _107635 _107636) = (term718 A B C P t _107635 p _107634 _107636).
Proof. exact (@lem8130257 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130264 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term514 A B C P t _107633 _107635 _107636) = (term514 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term514 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130265 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term716 A B C P _107633 p t _107634 _107635 _107636) = (term719 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130264 A B C P t _107633 _107635 _107636) (@lem8130258 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130276 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term715 A B C P p _107633 t _107634 _107635 _107636) = (term719 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (TRANS (@lem8130243 A B C P _107633 p t _107634 _107635 _107636) (@lem8130265 A B C P _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130277 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (s : P -> A) (_107636 : P) : (term631 A B C P lt2 z _107633 _107634 _107635 s _107636) = (term631 A B C P lt2 z _107633 _107634 _107635 s _107636).
Proof. exact (eq_refl (term631 A B C P lt2 z _107633 _107634 _107635 s _107636)). Qed.
Lemma lem8130278 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term714 A B C P lt2 z s p _107633 t _107634 _107635 _107636) = (term720 A B C P lt2 z s _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130277 A B C P lt2 z _107633 _107634 _107635 s _107636) (@lem8130276 A B C P _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130289 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term613 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term720 A B C P lt2 z s _107633 t _107635 p _107634 _107636).
Proof. exact (TRANS (@lem8130228 A B C P lt2 z s p _107633 t _107634 _107635 _107636) (@lem8130278 A B C P lt2 z s _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130290 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term547 A B P p _107633 _107636) = (term547 A B P p _107633 _107636).
Proof. exact (eq_refl (term547 A B P p _107633 _107636)). Qed.
Lemma lem8130291 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term721 A B C P lt2 z s _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130290 A B P p _107633 _107636) (@lem8130289 A B C P lt2 z s _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130295 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130296 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term721 A B C P lt2 z s _107633 t _107635 p _107634 _107636) = (term722 A B C P lt2 z s _107633 t _107635 p _107634 _107636).
Proof. exact (@lem8130295 (term541 A B C P lt2 z _107633 _107634 _107635 s _107636) (term546 A B P p _107633 _107636) (term719 A B C P _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130310 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130311 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term723 A B C P _107633 t _107635 p _107634 _107636) = (term724 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (@lem8130310 (term495 A B C P t _107633 _107635 _107636) (term546 A B P p _107633 _107636) (term718 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130325 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130326 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term725 A B C P _107633 t _107635 p _107634 _107636) = (term726 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (@lem8130325 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107633 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130342 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term514 A B C P t _107633 _107635 _107636) = (term514 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term514 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130343 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term724 A B C P _107633 t _107635 p _107634 _107636) = (term727 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130342 A B C P t _107633 _107635 _107636) (@lem8130326 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130354 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term723 A B C P _107633 t _107635 p _107634 _107636) = (term727 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130311 A B C P _107633 t _107635 p _107634 _107636) (@lem8130343 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130355 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (s : P -> A) (_107636 : P) : (term631 A B C P lt2 z _107633 _107634 _107635 s _107636) = (term631 A B C P lt2 z _107633 _107634 _107635 s _107636).
Proof. exact (eq_refl (term631 A B C P lt2 z _107633 _107634 _107635 s _107636)). Qed.
Lemma lem8130356 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term722 A B C P lt2 z s _107633 t _107635 p _107634 _107636) = (term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130355 A B C P lt2 z _107633 _107634 _107635 s _107636) (@lem8130354 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130367 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term721 A B C P lt2 z s _107633 t _107635 p _107634 _107636) = (term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130296 A B C P lt2 z s _107633 t _107635 p _107634 _107636) (@lem8130356 A B C P lt2 z s t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130368 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130291 A B C P lt2 z s _107633 t _107635 p _107634 _107636) (@lem8130367 A B C P lt2 z s t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8130370 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term729 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term730 A B C P lt2 z s t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130369) (@lem8130368 A B C P lt2 z s t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130394 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130395 {A B C P : Type'} (_107633 : A -> B) (p : type560 A B P) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term715 A B C P p _107633 t _107634 _107635 _107636) = (term716 A B C P _107633 p t _107634 _107635 _107636).
Proof. exact (@lem8130394 (term495 A B C P t _107633 _107635 _107636) (term546 A B P p _107634 _107636) (term497 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130409 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8130410 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term717 A B C P p t _107634 _107635 _107636) = (term718 A B C P t _107635 p _107634 _107636).
Proof. exact (@lem8130409 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130416 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term514 A B C P t _107633 _107635 _107636) = (term514 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term514 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130417 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term716 A B C P _107633 p t _107634 _107635 _107636) = (term719 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130416 A B C P t _107633 _107635 _107636) (@lem8130410 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130428 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term715 A B C P p _107633 t _107634 _107635 _107636) = (term719 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (TRANS (@lem8130395 A B C P _107633 p t _107634 _107635 _107636) (@lem8130417 A B C P _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130429 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term547 A B P p _107633 _107636) = (term547 A B P p _107633 _107636).
Proof. exact (eq_refl (term547 A B P p _107633 _107636)). Qed.
Lemma lem8130430 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term731 A B C P p _107633 t _107634 _107635 _107636) = (term723 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130429 A B P p _107633 _107636) (@lem8130428 A B C P _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130434 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130435 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term723 A B C P _107633 t _107635 p _107634 _107636) = (term724 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (@lem8130434 (term495 A B C P t _107633 _107635 _107636) (term546 A B P p _107633 _107636) (term718 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130449 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130450 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term725 A B C P _107633 t _107635 p _107634 _107636) = (term726 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (@lem8130449 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107633 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130466 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term514 A B C P t _107633 _107635 _107636) = (term514 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term514 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130467 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term724 A B C P _107633 t _107635 p _107634 _107636) = (term727 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130466 A B C P t _107633 _107635 _107636) (@lem8130450 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130478 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term723 A B C P _107633 t _107635 p _107634 _107636) = (term727 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130435 A B C P _107633 t _107635 p _107634 _107636) (@lem8130467 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130479 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term731 A B C P p _107633 t _107634 _107635 _107636) = (term727 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130430 A B C P _107633 t _107635 p _107634 _107636) (@lem8130478 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130480 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (s : P -> A) (_107636 : P) : (term631 A B C P lt2 z _107633 _107634 _107635 s _107636) = (term631 A B C P lt2 z _107633 _107634 _107635 s _107636).
Proof. exact (eq_refl (term631 A B C P lt2 z _107633 _107634 _107635 s _107636)). Qed.
Lemma lem8130481 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636) = (term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130480 A B C P lt2 z _107633 _107634 _107635 s _107636) (@lem8130479 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130492 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : ((term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636)) = ((term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636) = (term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636)).
Proof. exact (MK_COMB (@lem8130370 A B C P lt2 z s t _107635 _107633 p _107634 _107636) (@lem8130481 A B C P lt2 z s t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130494 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8130495 (x : Prop) : (x = x) = True.
Proof. exact (@lem8130494 Prop x). Qed.
Lemma lem8130496 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : ((term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636) = (term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636)) = True.
Proof. exact (@lem8130495 (term728 A B C P lt2 z s t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130497 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : ((term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636)) = True.
Proof. exact (TRANS (@lem8130492 A B C P lt2 z s t _107635 _107633 p _107634 _107636) (@lem8130496 A B C P lt2 z s t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130498 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : True = ((term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636)).
Proof. exact (SYM (@lem8130497 A B C P lt2 z s p _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130499 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (s : P -> A) (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term614 A B C P p lt2 z s _107633 t _107634 _107635 _107636) = (term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636).
Proof. exact (EQ_MP (@lem8130498 A B C P lt2 z s p _107633 t _107634 _107635 _107636) (@lem0)). Qed.
Lemma lem8130500 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636.
Proof. exact (EQ_MP (@lem8130499 A B C P lt2 z s p _107633 t _107634 _107635 _107636) (@lem8128863 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8130502 (b : Prop) (a : Prop) : (a \/ b) = (term646 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8130503 {A B C P : Type'} (p : type560 A B P) (t : type554 A B C P) (lt2 : type1402 A) (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (s : P -> A) (_107636 : P) : (term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636) = (term733 A B C P p t lt2 z _107633 _107634 _107635 s _107636).
Proof. exact (@lem8130502 (term731 A B C P p _107633 t _107634 _107635 _107636) (term541 A B C P lt2 z _107633 _107634 _107635 s _107636)). Qed.
Lemma lem8130505 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8130506 {A B C P : Type'} (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term734 A B C P p _107633 t _107634 _107635 _107636) = (term735 A B C P p _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130505 (term546 A B P p _107633 _107636) (term715 A B C P p _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130508 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130509 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term652 A B P p _107633 _107636) = (term489 A B P p _107633 _107636).
Proof. exact (@lem8130508 (term489 A B P p _107633 _107636)). Qed.
Lemma lem8130510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8130511 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term653 A B P p _107633 _107636) = (term490 A B P p _107633 _107636).
Proof. exact (MK_COMB (@lem8130510) (@lem8130509 A B P p _107633 _107636)). Qed.
Lemma lem8130513 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8130514 {A B C P : Type'} (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term736 A B C P p _107633 t _107634 _107635 _107636) = (term737 A B C P p _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130513 (term546 A B P p _107634 _107636) (term516 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130516 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130517 {A B P : Type'} (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term652 A B P p _107634 _107636) = (term489 A B P p _107634 _107636).
Proof. exact (@lem8130516 (term489 A B P p _107634 _107636)). Qed.
Lemma lem8130518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8130519 {A B P : Type'} (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term653 A B P p _107634 _107636) = (term490 A B P p _107634 _107636).
Proof. exact (MK_COMB (@lem8130518) (@lem8130517 A B P p _107634 _107636)). Qed.
Lemma lem8130521 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8130522 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term738 A B C P _107633 t _107634 _107635 _107636) = (term739 A B C P _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130521 (term495 A B C P t _107633 _107635 _107636) (term497 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130524 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130525 {A B C P : Type'} (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term658 A B C P t _107634 _107635 _107636) = (term495 A B C P t _107634 _107635 _107636).
Proof. exact (@lem8130524 (term495 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130526 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term499 A B C P t _107633 _107635 _107636) = (term499 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term499 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130527 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term739 A B C P _107633 t _107634 _107635 _107636) = (term501 A B C P _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130526 A B C P t _107633 _107635 _107636) (@lem8130525 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130528 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term738 A B C P _107633 t _107634 _107635 _107636) = (term501 A B C P _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8130522 A B C P _107633 t _107634 _107635 _107636) (@lem8130527 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130529 {A B C P : Type'} (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term737 A B C P p _107633 t _107634 _107635 _107636) = (term740 A B C P p _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130519 A B P p _107634 _107636) (@lem8130528 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130530 {A B C P : Type'} (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term736 A B C P p _107633 t _107634 _107635 _107636) = (term740 A B C P p _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8130514 A B C P p _107633 t _107634 _107635 _107636) (@lem8130529 A B C P p _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130531 {A B C P : Type'} (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term735 A B C P p _107633 t _107634 _107635 _107636) = (term741 A B C P p _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130511 A B P p _107633 _107636) (@lem8130530 A B C P p _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130532 {A B C P : Type'} (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term734 A B C P p _107633 t _107634 _107635 _107636) = (term741 A B C P p _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8130506 A B C P p _107633 t _107634 _107635 _107636) (@lem8130531 A B C P p _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130533 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8130534 {A B C P : Type'} (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term742 A B C P p _107633 t _107634 _107635 _107636) = (term743 A B C P p _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130533) (@lem8130532 A B C P p _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130535 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (s : P -> A) (_107636 : P) : (term541 A B C P lt2 z _107633 _107634 _107635 s _107636) = (term541 A B C P lt2 z _107633 _107634 _107635 s _107636).
Proof. exact (eq_refl (term541 A B C P lt2 z _107633 _107634 _107635 s _107636)). Qed.
Lemma lem8130536 {A B C P : Type'} (p : type560 A B P) (t : type554 A B C P) (lt2 : type1402 A) (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (s : P -> A) (_107636 : P) : (term733 A B C P p t lt2 z _107633 _107634 _107635 s _107636) = (term744 A B C P p t lt2 z _107633 _107634 _107635 s _107636).
Proof. exact (MK_COMB (@lem8130534 A B C P p _107633 t _107634 _107635 _107636) (@lem8130535 A B C P lt2 z _107633 _107634 _107635 s _107636)). Qed.
Lemma lem8130537 {A B C P : Type'} (p : type560 A B P) (t : type554 A B C P) (lt2 : type1402 A) (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (s : P -> A) (_107636 : P) : (term732 A B C P lt2 z s p _107633 t _107634 _107635 _107636) = (term744 A B C P p t lt2 z _107633 _107634 _107635 s _107636).
Proof. exact (TRANS (@lem8130503 A B C P p t lt2 z _107633 _107634 _107635 s _107636) (@lem8130536 A B C P p t lt2 z _107633 _107634 _107635 s _107636)). Qed.
Lemma lem8130539 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term497 A B C P t f x a) (h2 : term501 A B C P f t g x a) : term501 A B C P f t g x a.
Proof. exact (conj (@lem8130204 A B C P t f x a h1) (@lem8130211 A B C P f t g x a h2)). Qed.
Lemma lem8130540 {A B C P : Type'} (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term497 A B C P t f x a) (h2 : term501 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term740 A B C P p f t g x a.
Proof. exact (conj (@lem8130196 A B P p lt2 s a f g h3) (@lem8130539 A B C P f t g x a h1 h2)). Qed.
Lemma lem8130541 {A B C P : Type'} (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term497 A B C P t f x a) (h2 : term501 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term741 A B C P p f t g x a.
Proof. exact (conj (@lem8130189 A B P p lt2 s a f g h3) (@lem8130540 A B C P t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8130543 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term744 A B C P p t lt2 z _107633 _107634 _107635 s _107636.
Proof. exact (EQ_MP (@lem8130537 A B C P p t lt2 z _107633 _107634 _107635 s _107636) (@lem8130500 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8130544 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term744 A B C P p t lt2 z _107633 _107634 _107635 s _107636.
Proof. exact (@lem8130543 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1). Qed.
Lemma lem8130545 {A B C P : Type'} (f : A -> B) (g : A -> B) (x : C) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term744 A B C P p t lt2 z f g x s a.
Proof. exact (@lem8130544 A B C P f g x a p lt2 s z t h1). Qed.
Lemma lem8130548 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term541 A B C P lt2 z f g x s a.
Proof. exact (@lem8130545 A B C P f g x a p lt2 s z t h1 (@lem8130541 A B C P t x p lt2 s a f g h2 h3 h4)). Qed.
Lemma lem8130549 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term665 A B C P lt2 z f g x s a.
Proof. exact (fun h0 : term666 A B C P lt2 z f g x s a => @lem8130548 A B C P z t x p lt2 s a f g h1 h2 h3 h4). Qed.
Lemma lem8130551 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130552 {A B C P : Type'} (lt2 : type1402 A) (z : type517 A B C P) (f : A -> B) (g : A -> B) (x : C) (s : P -> A) (a : P) : (term665 A B C P lt2 z f g x s a) = (term541 A B C P lt2 z f g x s a).
Proof. exact (@lem8130551 (term541 A B C P lt2 z f g x s a)). Qed.
Lemma lem8130553 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term541 A B C P lt2 z f g x s a.
Proof. exact (EQ_MP (@lem8130552 A B C P lt2 z f g x s a) (@lem8130549 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8130559 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8130560 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : (term486 A B P lt2 s a f g _107637) = (term667 A B P f g lt2 _107637 s a).
Proof. exact (@lem8130559 ((@I (A -> B) f _107637) = (@I (A -> B) g _107637)) (term483 A P lt2 _107637 s a)). Qed.
Lemma lem8130568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8130569 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : (term668 A B P lt2 s a f g _107637) = (term669 A B P f g lt2 _107637 s a).
Proof. exact (MK_COMB (@lem8130568) (@lem8130560 A B P f g lt2 _107637 s a)). Qed.
Lemma lem8130577 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : (term667 A B P f g lt2 _107637 s a) = (term667 A B P f g lt2 _107637 s a).
Proof. exact (eq_refl (term667 A B P f g lt2 _107637 s a)). Qed.
Lemma lem8130578 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : ((term486 A B P lt2 s a f g _107637) = (term667 A B P f g lt2 _107637 s a)) = ((term667 A B P f g lt2 _107637 s a) = (term667 A B P f g lt2 _107637 s a)).
Proof. exact (MK_COMB (@lem8130569 A B P f g lt2 _107637 s a) (@lem8130577 A B P f g lt2 _107637 s a)). Qed.
Lemma lem8130580 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8130581 (x : Prop) : (x = x) = True.
Proof. exact (@lem8130580 Prop x). Qed.
Lemma lem8130582 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : ((term667 A B P f g lt2 _107637 s a) = (term667 A B P f g lt2 _107637 s a)) = True.
Proof. exact (@lem8130581 (term667 A B P f g lt2 _107637 s a)). Qed.
Lemma lem8130583 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : ((term486 A B P lt2 s a f g _107637) = (term667 A B P f g lt2 _107637 s a)) = True.
Proof. exact (TRANS (@lem8130578 A B P f g lt2 _107637 s a) (@lem8130582 A B P f g lt2 _107637 s a)). Qed.
Lemma lem8130584 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : True = ((term486 A B P lt2 s a f g _107637) = (term667 A B P f g lt2 _107637 s a)).
Proof. exact (SYM (@lem8130583 A B P f g lt2 _107637 s a)). Qed.
Lemma lem8130585 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : (term486 A B P lt2 s a f g _107637) = (term667 A B P f g lt2 _107637 s a).
Proof. exact (EQ_MP (@lem8130584 A B P f g lt2 _107637 s a) (@lem0)). Qed.
Lemma lem8130586 {A B P : Type'} (_107637 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term667 A B P f g lt2 _107637 s a.
Proof. exact (EQ_MP (@lem8130585 A B P f g lt2 _107637 s a) (@lem8128793 A B P _107637 p lt2 s a f g h1)). Qed.
Lemma lem8130588 (b : Prop) (a : Prop) : (a \/ b) = (term646 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8130589 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107637 : A) : (term667 A B P f g lt2 _107637 s a) = (term670 A B P lt2 s a f g _107637).
Proof. exact (@lem8130588 (term483 A P lt2 _107637 s a) ((@I (A -> B) f _107637) = (@I (A -> B) g _107637))). Qed.
Lemma lem8130591 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130592 {A P : Type'} (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : (term671 A P lt2 _107637 s a) = (term481 A P lt2 _107637 s a).
Proof. exact (@lem8130591 (term481 A P lt2 _107637 s a)). Qed.
Lemma lem8130593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8130594 {A P : Type'} (lt2 : type1402 A) (_107637 : A) (s : P -> A) (a : P) : (term672 A P lt2 _107637 s a) = (term673 A P lt2 _107637 s a).
Proof. exact (MK_COMB (@lem8130593) (@lem8130592 A P lt2 _107637 s a)). Qed.
Lemma lem8130595 {A B : Type'} (f : A -> B) (g : A -> B) (_107637 : A) : ((@I (A -> B) f _107637) = (@I (A -> B) g _107637)) = ((@I (A -> B) f _107637) = (@I (A -> B) g _107637)).
Proof. exact (eq_refl ((@I (A -> B) f _107637) = (@I (A -> B) g _107637))). Qed.
Lemma lem8130596 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107637 : A) : (term670 A B P lt2 s a f g _107637) = (term674 A B P lt2 s a f g _107637).
Proof. exact (MK_COMB (@lem8130594 A P lt2 _107637 s a) (@lem8130595 A B f g _107637)). Qed.
Lemma lem8130597 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107637 : A) : (term667 A B P f g lt2 _107637 s a) = (term674 A B P lt2 s a f g _107637).
Proof. exact (TRANS (@lem8130589 A B P lt2 s a f g _107637) (@lem8130596 A B P lt2 s a f g _107637)). Qed.
Lemma lem8130600 {A B P : Type'} (_107637 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term674 A B P lt2 s a f g _107637.
Proof. exact (EQ_MP (@lem8130597 A B P lt2 s a f g _107637) (@lem8130586 A B P _107637 p lt2 s a f g h1)). Qed.
Lemma lem8130601 {A B P : Type'} (_107637 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term674 A B P lt2 s a f g _107637.
Proof. exact (@lem8130600 A B P _107637 p lt2 s a f g h1). Qed.
Lemma lem8130602 {A B C P : Type'} (z : type517 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term156 A B P p lt2 s a f g) : term675 A B C P lt2 s z f g x a.
Proof. exact (@lem8130601 A B P (term524 A B C P z f g x a) p lt2 s a f g h1). Qed.
Lemma lem8130605 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : (term527 A B C P z f g x a) = (term530 A B C P z f g x a).
Proof. exact (@lem8130602 A B C P z x p lt2 s a f g h4 (@lem8130553 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8130606 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term676 A B C P z f g x a.
Proof. exact (fun h0 : term534 A B C P z f g x a => @lem8130605 A B C P z t x p lt2 s a f g h1 h2 h3 h4). Qed.
Lemma lem8130608 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130609 {A B C P : Type'} (z : type517 A B C P) (f : A -> B) (g : A -> B) (x : C) (a : P) : (term676 A B C P z f g x a) = ((term527 A B C P z f g x a) = (term530 A B C P z f g x a)).
Proof. exact (@lem8130608 ((term527 A B C P z f g x a) = (term530 A B C P z f g x a))). Qed.
Lemma lem8130610 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : (term527 A B C P z f g x a) = (term530 A B C P z f g x a).
Proof. exact (EQ_MP (@lem8130609 A B C P z f g x a) (@lem8130606 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8130612 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term495 A B C P t g x a.
Proof. exact (proj2 (@lem8128409 A B C P f t g x a h1)). Qed.
Lemma lem8130613 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term621 A B C P t g x a.
Proof. exact (fun h0 : term497 A B C P t g x a => @lem8130612 A B C P f t g x a h1). Qed.
Lemma lem8130615 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130616 {A B C P : Type'} (t : type554 A B C P) (g : A -> B) (x : C) (a : P) : (term621 A B C P t g x a) = (term495 A B C P t g x a).
Proof. exact (@lem8130615 (term495 A B C P t g x a)). Qed.
Lemma lem8130617 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term495 A B C P t g x a.
Proof. exact (EQ_MP (@lem8130616 A B C P t g x a) (@lem8130613 A B C P f t g x a h1)). Qed.
Lemma lem8130633 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130634 {A B C P : Type'} (z : type517 A B C P) (p : type560 A B P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term617 A B C P p z _107633 t _107634 _107635 _107636) = (term745 A B C P z p _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130633 (term534 A B C P z _107633 _107634 _107635 _107636) (term546 A B P p _107634 _107636) (term516 A B C P _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130650 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130651 {A B C P : Type'} (_107633 : A -> B) (p : type560 A B P) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term715 A B C P p _107633 t _107634 _107635 _107636) = (term716 A B C P _107633 p t _107634 _107635 _107636).
Proof. exact (@lem8130650 (term495 A B C P t _107633 _107635 _107636) (term546 A B P p _107634 _107636) (term497 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130665 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8130666 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term717 A B C P p t _107634 _107635 _107636) = (term718 A B C P t _107635 p _107634 _107636).
Proof. exact (@lem8130665 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130672 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term514 A B C P t _107633 _107635 _107636) = (term514 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term514 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130673 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term716 A B C P _107633 p t _107634 _107635 _107636) = (term719 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130672 A B C P t _107633 _107635 _107636) (@lem8130666 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130684 {A B C P : Type'} (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term715 A B C P p _107633 t _107634 _107635 _107636) = (term719 A B C P _107633 t _107635 p _107634 _107636).
Proof. exact (TRANS (@lem8130651 A B C P _107633 p t _107634 _107635 _107636) (@lem8130673 A B C P _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130685 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term678 A B C P z _107633 _107634 _107635 _107636) = (term678 A B C P z _107633 _107634 _107635 _107636).
Proof. exact (eq_refl (term678 A B C P z _107633 _107634 _107635 _107636)). Qed.
Lemma lem8130686 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term745 A B C P z p _107633 t _107634 _107635 _107636) = (term746 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130685 A B C P z _107633 _107634 _107635 _107636) (@lem8130684 A B C P _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130690 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130691 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term746 A B C P z _107633 t _107635 p _107634 _107636) = (term747 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (@lem8130690 (term495 A B C P t _107633 _107635 _107636) (term534 A B C P z _107633 _107634 _107635 _107636) (term718 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130719 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term745 A B C P z p _107633 t _107634 _107635 _107636) = (term747 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (TRANS (@lem8130686 A B C P z _107633 t _107635 p _107634 _107636) (@lem8130691 A B C P z _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130720 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term617 A B C P p z _107633 t _107634 _107635 _107636) = (term747 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (TRANS (@lem8130634 A B C P z p _107633 t _107634 _107635 _107636) (@lem8130719 A B C P z _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130721 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term547 A B P p _107633 _107636) = (term547 A B P p _107633 _107636).
Proof. exact (eq_refl (term547 A B P p _107633 _107636)). Qed.
Lemma lem8130722 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term618 A B C P p z _107633 t _107634 _107635 _107636) = (term748 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130721 A B P p _107633 _107636) (@lem8130720 A B C P z _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130726 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130727 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term748 A B C P z _107633 t _107635 p _107634 _107636) = (term749 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (@lem8130726 (term495 A B C P t _107633 _107635 _107636) (term546 A B P p _107633 _107636) (term750 A B C P z _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130741 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130742 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term751 A B C P z _107633 t _107635 p _107634 _107636) = (term752 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (@lem8130741 (term534 A B C P z _107633 _107634 _107635 _107636) (term546 A B P p _107633 _107636) (term718 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130758 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130759 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term725 A B C P _107633 t _107635 p _107634 _107636) = (term726 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (@lem8130758 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107633 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130775 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term678 A B C P z _107633 _107634 _107635 _107636) = (term678 A B C P z _107633 _107634 _107635 _107636).
Proof. exact (eq_refl (term678 A B C P z _107633 _107634 _107635 _107636)). Qed.
Lemma lem8130776 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term752 A B C P z _107633 t _107635 p _107634 _107636) = (term753 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130775 A B C P z _107633 _107634 _107635 _107636) (@lem8130759 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130787 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term751 A B C P z _107633 t _107635 p _107634 _107636) = (term753 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130742 A B C P z _107633 t _107635 p _107634 _107636) (@lem8130776 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130788 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term514 A B C P t _107633 _107635 _107636) = (term514 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term514 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130789 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term749 A B C P z _107633 t _107635 p _107634 _107636) = (term754 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130788 A B C P t _107633 _107635 _107636) (@lem8130787 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130800 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term748 A B C P z _107633 t _107635 p _107634 _107636) = (term754 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130727 A B C P z _107633 t _107635 p _107634 _107636) (@lem8130789 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130801 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term618 A B C P p z _107633 t _107634 _107635 _107636) = (term754 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130722 A B C P z _107633 t _107635 p _107634 _107636) (@lem8130800 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8130803 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term755 A B C P p z _107633 t _107634 _107635 _107636) = (term756 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130802) (@lem8130801 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130827 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130828 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (p : type560 A B P) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term757 A B C P p z _107633 t _107634 _107635 _107636) = (term758 A B C P z _107633 p t _107634 _107635 _107636).
Proof. exact (@lem8130827 (term534 A B C P z _107633 _107634 _107635 _107636) (term546 A B P p _107634 _107636) (term497 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130844 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8130845 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term717 A B C P p t _107634 _107635 _107636) = (term718 A B C P t _107635 p _107634 _107636).
Proof. exact (@lem8130844 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130851 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term678 A B C P z _107633 _107634 _107635 _107636) = (term678 A B C P z _107633 _107634 _107635 _107636).
Proof. exact (eq_refl (term678 A B C P z _107633 _107634 _107635 _107636)). Qed.
Lemma lem8130852 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term758 A B C P z _107633 p t _107634 _107635 _107636) = (term750 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130851 A B C P z _107633 _107634 _107635 _107636) (@lem8130845 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130863 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term757 A B C P p z _107633 t _107634 _107635 _107636) = (term750 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (TRANS (@lem8130828 A B C P z _107633 p t _107634 _107635 _107636) (@lem8130852 A B C P z _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130864 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term547 A B P p _107633 _107636) = (term547 A B P p _107633 _107636).
Proof. exact (eq_refl (term547 A B P p _107633 _107636)). Qed.
Lemma lem8130865 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term759 A B C P p z _107633 t _107634 _107635 _107636) = (term751 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130864 A B P p _107633 _107636) (@lem8130863 A B C P z _107633 t _107635 p _107634 _107636)). Qed.
Lemma lem8130869 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130870 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107635 : C) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term751 A B C P z _107633 t _107635 p _107634 _107636) = (term752 A B C P z _107633 t _107635 p _107634 _107636).
Proof. exact (@lem8130869 (term534 A B C P z _107633 _107634 _107635 _107636) (term546 A B P p _107633 _107636) (term718 A B C P t _107635 p _107634 _107636)). Qed.
Lemma lem8130886 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8130887 {A B C P : Type'} (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term725 A B C P _107633 t _107635 p _107634 _107636) = (term726 A B C P t _107635 _107633 p _107634 _107636).
Proof. exact (@lem8130886 (term497 A B C P t _107634 _107635 _107636) (term546 A B P p _107633 _107636) (term546 A B P p _107634 _107636)). Qed.
Lemma lem8130903 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term678 A B C P z _107633 _107634 _107635 _107636) = (term678 A B C P z _107633 _107634 _107635 _107636).
Proof. exact (eq_refl (term678 A B C P z _107633 _107634 _107635 _107636)). Qed.
Lemma lem8130904 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term752 A B C P z _107633 t _107635 p _107634 _107636) = (term753 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130903 A B C P z _107633 _107634 _107635 _107636) (@lem8130887 A B C P t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130915 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term751 A B C P z _107633 t _107635 p _107634 _107636) = (term753 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130870 A B C P z _107633 t _107635 p _107634 _107636) (@lem8130904 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130916 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term759 A B C P p z _107633 t _107634 _107635 _107636) = (term753 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (TRANS (@lem8130865 A B C P z _107633 t _107635 p _107634 _107636) (@lem8130915 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130917 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term514 A B C P t _107633 _107635 _107636) = (term514 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term514 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130918 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term760 A B C P p z _107633 t _107634 _107635 _107636) = (term754 A B C P z t _107635 _107633 p _107634 _107636).
Proof. exact (MK_COMB (@lem8130917 A B C P t _107633 _107635 _107636) (@lem8130916 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130929 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : ((term618 A B C P p z _107633 t _107634 _107635 _107636) = (term760 A B C P p z _107633 t _107634 _107635 _107636)) = ((term754 A B C P z t _107635 _107633 p _107634 _107636) = (term754 A B C P z t _107635 _107633 p _107634 _107636)).
Proof. exact (MK_COMB (@lem8130803 A B C P z t _107635 _107633 p _107634 _107636) (@lem8130918 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130931 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8130932 (x : Prop) : (x = x) = True.
Proof. exact (@lem8130931 Prop x). Qed.
Lemma lem8130933 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (_107635 : C) (_107633 : A -> B) (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : ((term754 A B C P z t _107635 _107633 p _107634 _107636) = (term754 A B C P z t _107635 _107633 p _107634 _107636)) = True.
Proof. exact (@lem8130932 (term754 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130934 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : ((term618 A B C P p z _107633 t _107634 _107635 _107636) = (term760 A B C P p z _107633 t _107634 _107635 _107636)) = True.
Proof. exact (TRANS (@lem8130929 A B C P z t _107635 _107633 p _107634 _107636) (@lem8130933 A B C P z t _107635 _107633 p _107634 _107636)). Qed.
Lemma lem8130935 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : True = ((term618 A B C P p z _107633 t _107634 _107635 _107636) = (term760 A B C P p z _107633 t _107634 _107635 _107636)).
Proof. exact (SYM (@lem8130934 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130936 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term618 A B C P p z _107633 t _107634 _107635 _107636) = (term760 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (EQ_MP (@lem8130935 A B C P p z _107633 t _107634 _107635 _107636) (@lem0)). Qed.
Lemma lem8130937 {A B C P : Type'} (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term760 A B C P p z _107633 t _107634 _107635 _107636.
Proof. exact (EQ_MP (@lem8130936 A B C P p z _107633 t _107634 _107635 _107636) (@lem8128885 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8130939 (b : Prop) (a : Prop) : (a \/ b) = (term646 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8130940 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107634 : A -> B) (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term760 A B C P p z _107633 t _107634 _107635 _107636) = (term761 A B C P p z _107634 t _107633 _107635 _107636).
Proof. exact (@lem8130939 (term759 A B C P p z _107633 t _107634 _107635 _107636) (term495 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130942 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8130943 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term762 A B C P p z _107633 t _107634 _107635 _107636) = (term763 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130942 (term546 A B P p _107633 _107636) (term757 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130945 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130946 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term652 A B P p _107633 _107636) = (term489 A B P p _107633 _107636).
Proof. exact (@lem8130945 (term489 A B P p _107633 _107636)). Qed.
Lemma lem8130947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8130948 {A B P : Type'} (p : type560 A B P) (_107633 : A -> B) (_107636 : P) : (term653 A B P p _107633 _107636) = (term490 A B P p _107633 _107636).
Proof. exact (MK_COMB (@lem8130947) (@lem8130946 A B P p _107633 _107636)). Qed.
Lemma lem8130950 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8130951 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term764 A B C P p z _107633 t _107634 _107635 _107636) = (term765 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130950 (term546 A B P p _107634 _107636) (term766 A B C P z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130953 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130954 {A B P : Type'} (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term652 A B P p _107634 _107636) = (term489 A B P p _107634 _107636).
Proof. exact (@lem8130953 (term489 A B P p _107634 _107636)). Qed.
Lemma lem8130955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8130956 {A B P : Type'} (p : type560 A B P) (_107634 : A -> B) (_107636 : P) : (term653 A B P p _107634 _107636) = (term490 A B P p _107634 _107636).
Proof. exact (MK_COMB (@lem8130955) (@lem8130954 A B P p _107634 _107636)). Qed.
Lemma lem8130958 (a : Prop) (b : Prop) : (term648 a b) = (term649 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8130959 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term767 A B C P z _107633 t _107634 _107635 _107636) = (term768 A B C P z _107633 t _107634 _107635 _107636).
Proof. exact (@lem8130958 (term534 A B C P z _107633 _107634 _107635 _107636) (term497 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130961 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130962 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term703 A B C P z _107633 _107634 _107635 _107636) = ((term527 A B C P z _107633 _107634 _107635 _107636) = (term530 A B C P z _107633 _107634 _107635 _107636)).
Proof. exact (@lem8130961 ((term527 A B C P z _107633 _107634 _107635 _107636) = (term530 A B C P z _107633 _107634 _107635 _107636))). Qed.
Lemma lem8130963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8130964 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term704 A B C P z _107633 _107634 _107635 _107636) = (term705 A B C P z _107633 _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130963) (@lem8130962 A B C P z _107633 _107634 _107635 _107636)). Qed.
Lemma lem8130966 (a : Prop) : (term288 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8130967 {A B C P : Type'} (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term658 A B C P t _107634 _107635 _107636) = (term495 A B C P t _107634 _107635 _107636).
Proof. exact (@lem8130966 (term495 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130968 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term768 A B C P z _107633 t _107634 _107635 _107636) = (term769 A B C P z _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130964 A B C P z _107633 _107634 _107635 _107636) (@lem8130967 A B C P t _107634 _107635 _107636)). Qed.
Lemma lem8130969 {A B C P : Type'} (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term767 A B C P z _107633 t _107634 _107635 _107636) = (term769 A B C P z _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8130959 A B C P z _107633 t _107634 _107635 _107636) (@lem8130968 A B C P z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130970 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term765 A B C P p z _107633 t _107634 _107635 _107636) = (term770 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130956 A B P p _107634 _107636) (@lem8130969 A B C P z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130971 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term764 A B C P p z _107633 t _107634 _107635 _107636) = (term770 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8130951 A B C P p z _107633 t _107634 _107635 _107636) (@lem8130970 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130972 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term763 A B C P p z _107633 t _107634 _107635 _107636) = (term771 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130948 A B P p _107633 _107636) (@lem8130971 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130973 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term762 A B C P p z _107633 t _107634 _107635 _107636) = (term771 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (TRANS (@lem8130943 A B C P p z _107633 t _107634 _107635 _107636) (@lem8130972 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130974 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8130975 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107633 : A -> B) (t : type554 A B C P) (_107634 : A -> B) (_107635 : C) (_107636 : P) : (term772 A B C P p z _107633 t _107634 _107635 _107636) = (term773 A B C P p z _107633 t _107634 _107635 _107636).
Proof. exact (MK_COMB (@lem8130974) (@lem8130973 A B C P p z _107633 t _107634 _107635 _107636)). Qed.
Lemma lem8130976 {A B C P : Type'} (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term495 A B C P t _107633 _107635 _107636) = (term495 A B C P t _107633 _107635 _107636).
Proof. exact (eq_refl (term495 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130977 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107634 : A -> B) (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term761 A B C P p z _107634 t _107633 _107635 _107636) = (term774 A B C P p z _107634 t _107633 _107635 _107636).
Proof. exact (MK_COMB (@lem8130975 A B C P p z _107633 t _107634 _107635 _107636) (@lem8130976 A B C P t _107633 _107635 _107636)). Qed.
Lemma lem8130978 {A B C P : Type'} (p : type560 A B P) (z : type517 A B C P) (_107634 : A -> B) (t : type554 A B C P) (_107633 : A -> B) (_107635 : C) (_107636 : P) : (term760 A B C P p z _107633 t _107634 _107635 _107636) = (term774 A B C P p z _107634 t _107633 _107635 _107636).
Proof. exact (TRANS (@lem8130940 A B C P p z _107634 t _107633 _107635 _107636) (@lem8130977 A B C P p z _107634 t _107633 _107635 _107636)). Qed.
Lemma lem8130980 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term769 A B C P z f t g x a.
Proof. exact (conj (@lem8130610 A B C P z t x p lt2 s a f g h1 h2 h3 h4) (@lem8130617 A B C P f t g x a h3)). Qed.
Lemma lem8130981 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term770 A B C P p z f t g x a.
Proof. exact (conj (@lem8130182 A B P p lt2 s a f g h4) (@lem8130980 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8130982 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term771 A B C P p z f t g x a.
Proof. exact (conj (@lem8130175 A B P p lt2 s a f g h4) (@lem8130981 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8130984 {A B C P : Type'} (_107634 : A -> B) (_107633 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term774 A B C P p z _107634 t _107633 _107635 _107636.
Proof. exact (EQ_MP (@lem8130978 A B C P p z _107634 t _107633 _107635 _107636) (@lem8130937 A B C P _107633 _107634 _107635 _107636 p lt2 s z t h1)). Qed.
Lemma lem8130985 {A B C P : Type'} (_107634 : A -> B) (_107633 : A -> B) (_107635 : C) (_107636 : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term774 A B C P p z _107634 t _107633 _107635 _107636.
Proof. exact (@lem8130984 A B C P _107634 _107633 _107635 _107636 p lt2 s z t h1). Qed.
Lemma lem8130986 {A B C P : Type'} (g : A -> B) (f : A -> B) (x : C) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (z : type517 A B C P) (t : type554 A B C P) (h1 : term467 A B C P p lt2 s z t) : term774 A B C P p z g t f x a.
Proof. exact (@lem8130985 A B C P g f x a p lt2 s z t h1). Qed.
Lemma lem8130989 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term497 A B C P t f x a) (h3 : term501 A B C P f t g x a) (h4 : term156 A B P p lt2 s a f g) : term495 A B C P t f x a.
Proof. exact (@lem8130986 A B C P g f x a p lt2 s z t h1 (@lem8130982 A B C P z t x p lt2 s a f g h1 h2 h3 h4)). Qed.
Lemma lem8130990 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term501 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term621 A B C P t f x a.
Proof. exact (fun h0 : term497 A B C P t f x a => @lem8130989 A B C P z t x p lt2 s a f g h1 h0 h2 h3). Qed.
Lemma lem8130992 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8130993 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term621 A B C P t f x a) = (term495 A B C P t f x a).
Proof. exact (@lem8130992 (term495 A B C P t f x a)). Qed.
Lemma lem8130994 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term501 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term495 A B C P t f x a.
Proof. exact (EQ_MP (@lem8130993 A B C P t f x a) (@lem8130990 A B C P z t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8130997 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8130999 {A B C P : Type'} (t : type554 A B C P) (f : A -> B) (x : C) (a : P) : (term497 A B C P t f x a) = (term712 A B C P t f x a).
Proof. exact (@lem8130997 (term495 A B C P t f x a)). Qed.
Lemma lem8131002 {A B C P : Type'} (f : A -> B) (t : type554 A B C P) (g : A -> B) (x : C) (a : P) (h1 : term501 A B C P f t g x a) : term712 A B C P t f x a.
Proof. exact (EQ_MP (@lem8130999 A B C P t f x a) (@lem8128795 A B C P f t g x a h1)). Qed.
Lemma lem8131005 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term501 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : False.
Proof. exact (@lem8131002 A B C P f t g x a h2 (@lem8130994 A B C P z t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8131006 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term501 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : term713.
Proof. exact (fun h0 : ~ False => @lem8131005 A B C P z t x p lt2 s a f g h1 h2 h3). Qed.
Lemma lem8131008 (p : Prop) : (term620 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8131009 : term713 = False.
Proof. exact (@lem8131008 False). Qed.
Lemma lem8131010 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term501 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8131009) (@lem8131006 A B C P z t x p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8131011 {A B C P : Type'} (z : type517 A B C P) (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term467 A B C P p lt2 s z t) (h2 : term290 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : False.
Proof. exact (or_elim (@lem8128076 A B C P f t g x a h2) (fun h0 : term505 A B C P f t g x a => @lem8129965 A B C P z t x p lt2 s a f g h1 h0 h3) (fun h0 : term501 A B C P f t g x a => @lem8131010 A B C P z t x p lt2 s a f g h1 h0 h3)). Qed.
Lemma lem8131012 {A B C P : Type'} (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term215 A B C P p lt2 s t) (h2 : term290 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : False.
Proof. exact (ex_elim (@lem8127774 A B C P p lt2 s t h1) (fun z : type517 A B C P => fun h0 : term469 A B C P p lt2 s t z => @lem8131011 A B C P z t x p lt2 s a f g h0 h2 h3)). Qed.
Lemma lem8131013 {A B C P : Type'} (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term215 A B C P p lt2 s t) (h2 : term290 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : (term290 A B C P f t g x a) = False.
Proof. exact (prop_ext (fun h4 : term290 A B C P f t g x a => @lem8131012 A B C P t x p lt2 s a f g h1 h2 h3) (fun h4 : False => @lem8127393 A B C P f t g x a h2)). Qed.
Lemma lem8131014 {A B C P : Type'} (t : type554 A B C P) (x : C) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term215 A B C P p lt2 s t) (h2 : term290 A B C P f t g x a) (h3 : term156 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8131013 A B C P t x p lt2 s a f g h1 h2 h3) (@lem8127393 A B C P f t g x a h2)). Qed.
Lemma lem8131015 {A B C P : Type'} (x : C) (t : type554 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term215 A B C P p lt2 s t) (h2 : term156 A B P p lt2 s a f g) : term289 A B C P f t g x a.
Proof. exact (fun h0 : term290 A B C P f t g x a => @lem8131014 A B C P t x p lt2 s a f g h1 h0 h2). Qed.
Lemma lem8131016 {A B C P : Type'} (x : C) (t : type554 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term215 A B C P p lt2 s t) (h2 : term156 A B P p lt2 s a f g) : (t f x a) = (t g x a).
Proof. exact (EQ_MP (@lem8127392 A B C P f t g x a) (@lem8131015 A B C P x t p lt2 s a f g h1 h2)). Qed.
Lemma lem8131021 {A B C P : Type'} (t : type554 A B C P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term215 A B C P p lt2 s t) (h2 : term156 A B P p lt2 s a f g) : term249 A B C P f t g a.
Proof. exact (fun x : C => @lem8131016 A B C P x t p lt2 s a f g h1 h2). Qed.
Lemma lem8131022 {A B C P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) (h1 : term215 A B C P p lt2 s t) : term251 A B C P p lt2 s f t g a.
Proof. exact (fun h0 : term156 A B P p lt2 s a f g => @lem8131021 A B C P t p lt2 s a f g h1 h0). Qed.
Lemma lem8131027 {A B C P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) (h1 : term215 A B C P p lt2 s t) : term255 A B C P p lt2 s f t g.
Proof. exact (fun a : P => @lem8131022 A B C P f g a p lt2 s t h1). Qed.
Lemma lem8131032 {A B C P : Type'} (f : A -> B) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) (h1 : term215 A B C P p lt2 s t) : term259 A B C P p lt2 s f t.
Proof. exact (fun g : A -> B => @lem8131027 A B C P f g p lt2 s t h1). Qed.
Lemma lem8131037 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) (h1 : term215 A B C P p lt2 s t) : term262 A B C P p lt2 s t.
Proof. exact (fun f : A -> B => @lem8131032 A B C P f p lt2 s t h1). Qed.
Lemma lem8131038 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type554 A B C P) : term264 A B C P p lt2 s t.
Proof. exact (fun h0 : term215 A B C P p lt2 s t => @lem8131037 A B C P p lt2 s t h0). Qed.
Lemma lem8131043 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : term268 A B C P p lt2 s.
Proof. exact (fun t : type554 A B C P => @lem8131038 A B C P p lt2 s t). Qed.
Lemma lem8131048 {A B C P : Type'} (p : type560 A B P) (lt2 : type1402 A) : term272 A B C P p lt2.
Proof. exact (fun s : P -> A => @lem8131043 A B C P p lt2 s). Qed.
Lemma lem8131053 {A B C P : Type'} (lt2 : type1402 A) : term276 A B C P lt2.
Proof. exact (fun p : type560 A B P => @lem8131048 A B C P p lt2). Qed.
Lemma lem8131058 {A B C P : Type'} : term280 A B C P.
Proof. exact (fun lt2 : type1402 A => @lem8131053 A B C P lt2). Qed.
Lemma lem8131059 {A B C P : Type'} : term282 A B C P.
Proof. exact (EQ_MP (@lem8127386 A B C P) (@lem8131058 A B C P)). Qed.
Lemma lem8131061 {A B C P : Type'} : term282 A B C P.
Proof. exact (@lem8127108 A B C P (@lem8131059 A B C P)). Qed.
Lemma lem8131062 {A B C P : Type'} (h1 : term283 A B C P) : False.
Proof. exact (@lem8131061 A B C P (@lem8127092 A B C P h1)). Qed.
Lemma lem8131063 {A B C P : Type'} (h1 : term283 A B C P) : (term283 A B C P) = False.
Proof. exact (prop_ext (fun h2 : term283 A B C P => @lem8131062 A B C P h1) (fun h2 : False => @lem8127092 A B C P h1)). Qed.
Lemma lem8131064 {A B C P : Type'} (h1 : term283 A B C P) : False.
Proof. exact (EQ_MP (@lem8131063 A B C P h1) (@lem8127092 A B C P h1)). Qed.
Lemma lem8131065 {A B C P : Type'} : term282 A B C P.
Proof. exact (fun h0 : term283 A B C P => @lem8131064 A B C P h0). Qed.
Lemma lem8131066 {A B C P : Type'} : term280 A B C P.
Proof. exact (EQ_MP (@lem8127091 A B C P) (@lem8131065 A B C P)). Qed.
Lemma lem8131067 {A B C P : Type'} : term279 A B C P.
Proof. exact (EQ_MP (@lem8127087 A B C P) (@lem8131066 A B C P)). Qed.
