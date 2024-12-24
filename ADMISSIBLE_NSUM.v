Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_NSUM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import NSUM_EQ_NUMSEG_spec.
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
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20669_spec.
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
Lemma lem8215180 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem8215181 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem8215182 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem8215181 t1) (@lem8215180 t1)). Qed.
Lemma lem8215183 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem8215182 t1 t2). Qed.
Lemma lem8215184 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem8215185 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem8215184 t1 t2) (@lem8215183 t1 t2)). Qed.
Lemma lem8215186 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem8215185 t1 t2 t3). Qed.
Lemma lem8215187 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem8215188 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem8215187 t1 t2 t3) (@lem8215186 t1 t2 t3)). Qed.
Lemma lem8215189 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem8215188 t1 t2 t3)). Qed.
Lemma lem8215190 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem8215191 (f : nat -> nat) (h1 : term7) : term8 f.
Proof. exact (@lem8215190 h1 f). Qed.
Lemma lem8215192 (f : nat -> nat) : (term8 f) = (term9 f).
Proof. exact (eq_refl (term8 f)). Qed.
Lemma lem8215193 (f : nat -> nat) (h1 : term7) : term9 f.
Proof. exact (EQ_MP (@lem8215192 f) (@lem8215191 f h1)). Qed.
Lemma lem8215194 (f : nat -> nat) (g : nat -> nat) (h1 : term7) : term10 f g.
Proof. exact (@lem8215193 f h1 g). Qed.
Lemma lem8215195 (f : nat -> nat) (g : nat -> nat) : (term10 f g) = (term11 f g).
Proof. exact (eq_refl (term10 f g)). Qed.
Lemma lem8215196 (f : nat -> nat) (g : nat -> nat) (h1 : term7) : term11 f g.
Proof. exact (EQ_MP (@lem8215195 f g) (@lem8215194 f g h1)). Qed.
Lemma lem8215197 (f : nat -> nat) (g : nat -> nat) (m : nat) (h1 : term7) : term12 f g m.
Proof. exact (@lem8215196 f g h1 m). Qed.
Lemma lem8215198 (f : nat -> nat) (m : nat) (g : nat -> nat) : (term12 f g m) = (term13 f m g).
Proof. exact (eq_refl (term12 f g m)). Qed.
Lemma lem8215199 (f : nat -> nat) (m : nat) (g : nat -> nat) (h1 : term7) : term13 f m g.
Proof. exact (EQ_MP (@lem8215198 f m g) (@lem8215197 f g m h1)). Qed.
Lemma lem8215200 (f : nat -> nat) (m : nat) (g : nat -> nat) (n : nat) (h1 : term7) : term14 f m g n.
Proof. exact (@lem8215199 f m g h1 n). Qed.
Lemma lem8215201 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term14 f m g n) = (term15 f m n g).
Proof. exact (eq_refl (term14 f m g n)). Qed.
Lemma lem8215202 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term7) : term15 f m n g.
Proof. exact (EQ_MP (@lem8215201 f m n g) (@lem8215200 f m g n h1)). Qed.
Lemma lem8215203 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term16 m n f g) : term16 m n f g.
Proof. exact (h1). Qed.
Lemma lem8215204 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term7) (h2 : term16 m n f g) : (term17 m n f) = (term17 m n g).
Proof. exact (@lem8215202 f m n g h1 (@lem8215203 m n f g h2)). Qed.
Lemma lem8215205 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term16 m n f g) : term18 f m n g.
Proof. exact (fun h0 : term7 => @lem8215204 m n f g h0 h1). Qed.
Lemma lem8215206 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem8215207 (m : nat) (n : nat) (f : nat -> nat) (g : nat -> nat) (h1 : term7) (h2 : term16 m n f g) : (term17 m n f) = (term17 m n g).
Proof. exact (@lem8215205 m n f g h2 (@lem8215206 h1)). Qed.
Lemma lem8215208 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) (h1 : term7) : term15 f m n g.
Proof. exact (fun h0 : term16 m n f g => @lem8215207 m n f g h1 h0). Qed.
Lemma lem8215209 (f : nat -> nat) (m : nat) (n : nat) (h1 : term7) : term19 f m n.
Proof. exact (fun g : nat -> nat => @lem8215208 f m n g h1). Qed.
Lemma lem8215210 (f : nat -> nat) (m : nat) (h1 : term7) : term20 f m.
Proof. exact (fun n : nat => @lem8215209 f m n h1). Qed.
Lemma lem8215211 (f : nat -> nat) (h1 : term7) : term21 f.
Proof. exact (fun m : nat => @lem8215210 f m h1). Qed.
Lemma lem8215212 (h1 : term7) : term22.
Proof. exact (fun f : nat -> nat => @lem8215211 f h1). Qed.
Lemma lem8215213 : term23.
Proof. exact (fun h0 : term7 => @lem8215212 h0). Qed.
Lemma lem8215214 : term22.
Proof. exact (@lem8215213 (@lem7044316)). Qed.
Lemma lem8215215 (f : nat -> nat) : term24 f.
Proof. exact (@lem8215214 f). Qed.
Lemma lem8215216 (f : nat -> nat) : (term24 f) = (term21 f).
Proof. exact (eq_refl (term24 f)). Qed.
Lemma lem8215217 (f : nat -> nat) : term21 f.
Proof. exact (EQ_MP (@lem8215216 f) (@lem8215215 f)). Qed.
Lemma lem8215218 (f : nat -> nat) (m : nat) : term25 f m.
Proof. exact (@lem8215217 f m). Qed.
Lemma lem8215219 (f : nat -> nat) (m : nat) : (term25 f m) = (term20 f m).
Proof. exact (eq_refl (term25 f m)). Qed.
Lemma lem8215220 (f : nat -> nat) (m : nat) : term20 f m.
Proof. exact (EQ_MP (@lem8215219 f m) (@lem8215218 f m)). Qed.
Lemma lem8215221 (f : nat -> nat) (m : nat) (n : nat) : term26 f m n.
Proof. exact (@lem8215220 f m n). Qed.
Lemma lem8215222 (f : nat -> nat) (m : nat) (n : nat) : (term26 f m n) = (term19 f m n).
Proof. exact (eq_refl (term26 f m n)). Qed.
Lemma lem8215223 (f : nat -> nat) (m : nat) (n : nat) : term19 f m n.
Proof. exact (EQ_MP (@lem8215222 f m n) (@lem8215221 f m n)). Qed.
Lemma lem8215224 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : term27 f m n g.
Proof. exact (@lem8215223 f m n g). Qed.
Lemma lem8215225 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : (term27 f m n g) = (term15 f m n g).
Proof. exact (eq_refl (term27 f m n g)). Qed.
Lemma lem8215227 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term28 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem8215228 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term28 _5106 _5107 P) = ((term29 _5106 _5107 P) = (term30 _5106 _5107 P)).
Proof. exact (eq_refl (term28 _5106 _5107 P)). Qed.
Lemma lem8215230 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term31 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8215231 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term31 _143449 _143452 _143456 _143457 _143462 p) = (term32 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term31 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8215232 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term32 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8215231 _143449 _143452 _143456 _143457 _143462 p) (@lem8215230 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8215233 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term33 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8215232 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8215234 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term33 _143449 _143452 _143456 _143457 _143462 p lt2) = (term34 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term33 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8215235 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term34 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8215234 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8215233 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8215236 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term35 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8215235 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8215237 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term35 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term36 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term35 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8215238 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term36 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8215237 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8215236 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8215239 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term37 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8215238 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8215240 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term37 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term38 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term37 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8215281 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term38 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8215240 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8215239 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8215282 {A B C P : Type'} (p : type542 B C P) (lt2 : type1470 A B) (s : type1313 A P) (t : type543 B C P) : (@admissible A C B nat (prod nat P) lt2 p s t) = (term39 A B C P p lt2 s t).
Proof. exact (@lem8215281 A C B nat (prod nat P) p lt2 s t). Qed.
Lemma lem8215283 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term40 A B C P lt2 a b p s h) = (term41 A B C P a b p lt2 s h).
Proof. exact (@lem8215282 A B C P (term42 B C P a b p) lt2 (term43 A P s) (term44 B C P h)). Qed.
Lemma lem8215301 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term29 _5106 _5107 P) = (term30 _5106 _5107 P).
Proof. exact (EQ_MP (@lem8215228 _5106 _5107 P) (@lem8215227 _5106 _5107 P)). Qed.
Lemma lem8215302 {P : Type'} (P' : type1310 P) : (term45 P P') = (term46 P P').
Proof. exact (@lem8215301 P nat P'). Qed.
Lemma lem8215303 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term47 A B C P a b p lt2 s f h g) = (term48 A B C P a b p lt2 s f h g).
Proof. exact (@lem8215302 P (term49 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8215304 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : prod nat P) : (term50 A B C P a b p lt2 s f h g a') = (term51 A B C P a b p lt2 s f h g a').
Proof. exact (eq_refl (term50 A B C P a b p lt2 s f h g a')). Qed.
Lemma lem8215305 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term52 A B C P a b p lt2 s f h g) = (term49 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun a' : prod nat P => @lem8215304 A B C P a b p lt2 s f h g a')). Qed.
Lemma lem8215306 {P : Type'} : (@all (prod nat P)) = (@all (prod nat P)).
Proof. exact (eq_refl (@all (prod nat P))). Qed.
Lemma lem8215307 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term47 A B C P a b p lt2 s f h g) = (term53 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8215306 P) (@lem8215305 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8215308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8215309 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term54 A B C P a b p lt2 s f h g) = (term55 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8215308) (@lem8215307 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8215310 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) (p2 : P) : (term56 A B C P a b p lt2 s f h g p1 p2) = (term57 A B C P a b p lt2 s f h g p1 p2).
Proof. exact (eq_refl (term56 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8215311 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term58 A B C P a b p lt2 s f h g p1) = (term59 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8215310 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8215312 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8215313 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term60 A B C P a b p lt2 s f h g p1) = (term61 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8215312 P) (@lem8215311 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8215314 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term62 A B C P a b p lt2 s f h g) = (term63 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8215313 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8215315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8215316 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term48 A B C P a b p lt2 s f h g) = (term64 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8215315) (@lem8215314 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8215317 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : ((term47 A B C P a b p lt2 s f h g) = (term48 A B C P a b p lt2 s f h g)) = ((term53 A B C P a b p lt2 s f h g) = (term64 A B C P a b p lt2 s f h g)).
Proof. exact (MK_COMB (@lem8215309 A B C P a b p lt2 s f h g) (@lem8215316 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8215318 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term53 A B C P a b p lt2 s f h g) = (term64 A B C P a b p lt2 s f h g).
Proof. exact (EQ_MP (@lem8215317 A B C P a b p lt2 s f h g) (@lem8215303 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8215336 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8215337 {B C P : Type'} (f : type542 B C P) (y : B -> C) : (term66 B C P f y) = (f y).
Proof. exact (@lem8215336 (B -> C) (type1310 P) f y). Qed.
Lemma lem8215338 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term67 B C P a b p f) = (term68 B C P a b p f).
Proof. exact (@lem8215337 B C P (term42 B C P a b p) f). Qed.
Lemma lem8215339 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (eq_refl (term68 B C P a b p f)). Qed.
Lemma lem8215340 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) : (term70 B C P a b p) = (term42 B C P a b p).
Proof. exact (fun_ext (fun f : B -> C => @lem8215339 B C P a b p f)). Qed.
Lemma lem8215341 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8215342 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term67 B C P a b p f) = (term68 B C P a b p f).
Proof. exact (MK_COMB (@lem8215340 B C P a b p) (@lem8215341 B C f)). Qed.
Lemma lem8215343 {P : Type'} : (@eq ((prod nat P) -> Prop)) = (@eq ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod nat P) -> Prop))). Qed.
Lemma lem8215344 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term71 B C P a b p f) = (term72 B C P a b p f).
Proof. exact (MK_COMB (@lem8215343 P) (@lem8215342 B C P a b p f)). Qed.
Lemma lem8215345 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (eq_refl (term68 B C P a b p f)). Qed.
Lemma lem8215346 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term67 B C P a b p f) = (term68 B C P a b p f)) = ((term68 B C P a b p f) = (term69 B C P a b p f)).
Proof. exact (MK_COMB (@lem8215344 B C P a b p f) (@lem8215345 B C P a b p f)). Qed.
Lemma lem8215347 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (EQ_MP (@lem8215346 B C P a b p f) (@lem8215338 B C P a b p f)). Qed.
Lemma lem8215364 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8215365 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p1 : nat) (p2 : P) : (term73 B C P a b p f p1 p2) = (term74 B C P a b p f p1 p2).
Proof. exact (MK_COMB (@lem8215347 B C P a b p f) (@lem8215364 P p1 p2)). Qed.
Lemma lem8215366 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8215367 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8215366 P k x). Qed.
Lemma lem8215368 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8215369 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8215368 P k x). Qed.
Lemma lem8215370 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8215371 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8215372 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8215371) (@lem8215367 P k x)). Qed.
Lemma lem8215373 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8215374 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8215375 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215374 k) (@lem8215373 P k x)). Qed.
Lemma lem8215376 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8215377 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215378 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8215377) (@lem8215376 k)). Qed.
Lemma lem8215379 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8215380 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215378 k) (@lem8215379 P k x)). Qed.
Lemma lem8215381 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8215375 P k x) (@lem8215380 P k x)). Qed.
Lemma lem8215382 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215381 P k x) (@lem8215372 P k x)). Qed.
Lemma lem8215383 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8215384 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215383 k) (@lem8215382 P k x)). Qed.
Lemma lem8215385 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215384 P k x) (@lem8215370 k)). Qed.
Lemma lem8215386 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8215387 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8215388 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8215387 P) (@lem8215369 P k x)). Qed.
Lemma lem8215389 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8215390 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8215391 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215390 P x) (@lem8215389 P k x)). Qed.
Lemma lem8215392 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8215393 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8215394 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8215393 P) (@lem8215392 P x)). Qed.
Lemma lem8215395 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8215396 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215394 P x) (@lem8215395 P k x)). Qed.
Lemma lem8215397 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8215391 P k x) (@lem8215396 P k x)). Qed.
Lemma lem8215398 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215397 P k x) (@lem8215388 P k x)). Qed.
Lemma lem8215399 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8215400 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215399 P x) (@lem8215398 P k x)). Qed.
Lemma lem8215401 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215400 P k x) (@lem8215386 P x)). Qed.
Lemma lem8215402 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term85 B C P a b p f) = (term85 B C P a b p f).
Proof. exact (eq_refl (term85 B C P a b p f)). Qed.
Lemma lem8215403 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term86 B C P a b p f k) = (term87 B C P a b p f k x).
Proof. exact (MK_COMB (@lem8215402 B C P a b p f) (@lem8215385 P k x)). Qed.
Lemma lem8215404 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term87 B C P a b p f k x) = (term88 B C P a k x b p f).
Proof. exact (eq_refl (term87 B C P a b p f k x)). Qed.
Lemma lem8215405 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) : (term89 B C P a b p f k) = (term89 B C P a b p f k).
Proof. exact (eq_refl (term89 B C P a b p f k)). Qed.
Lemma lem8215406 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term86 B C P a b p f k) = (term87 B C P a b p f k x)) = ((term86 B C P a b p f k) = (term88 B C P a k x b p f)).
Proof. exact (MK_COMB (@lem8215405 B C P a b p f k) (@lem8215404 B C P a k x b p f)). Qed.
Lemma lem8215407 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term86 B C P a b p f k) = (term90 B C P a k b p f).
Proof. exact (eq_refl (term86 B C P a b p f k)). Qed.
Lemma lem8215408 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8215409 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term89 B C P a b p f k) = (term91 B C P a k b p f).
Proof. exact (MK_COMB (@lem8215408 P) (@lem8215407 B C P a k b p f)). Qed.
Lemma lem8215410 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term88 B C P a k x b p f) = (term88 B C P a k x b p f).
Proof. exact (eq_refl (term88 B C P a k x b p f)). Qed.
Lemma lem8215411 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term86 B C P a b p f k) = (term88 B C P a k x b p f)) = ((term90 B C P a k b p f) = (term88 B C P a k x b p f)).
Proof. exact (MK_COMB (@lem8215409 B C P a k b p f) (@lem8215410 B C P a k x b p f)). Qed.
Lemma lem8215412 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : ((term86 B C P a b p f k) = (term87 B C P a b p f k x)) = ((term90 B C P a k b p f) = (term88 B C P a k x b p f)).
Proof. exact (TRANS (@lem8215406 B C P a k x b p f) (@lem8215411 B C P a k x b p f)). Qed.
Lemma lem8215413 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term90 B C P a k b p f) = (term88 B C P a k x b p f).
Proof. exact (EQ_MP (@lem8215412 B C P a k x b p f) (@lem8215403 B C P a b p f k x)). Qed.
Lemma lem8215414 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term92 B C P a k b p f x) = (term93 B C P a b p f k x).
Proof. exact (MK_COMB (@lem8215413 B C P a k x b p f) (@lem8215401 P k x)). Qed.
Lemma lem8215415 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term93 B C P a b p f k x) = (term94 B C P a b p f k x).
Proof. exact (eq_refl (term93 B C P a b p f k x)). Qed.
Lemma lem8215416 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term95 B C P a k b p f x) = (term95 B C P a k b p f x).
Proof. exact (eq_refl (term95 B C P a k b p f x)). Qed.
Lemma lem8215417 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p f x) = (term93 B C P a b p f k x)) = ((term92 B C P a k b p f x) = (term94 B C P a b p f k x)).
Proof. exact (MK_COMB (@lem8215416 B C P a k b p f x) (@lem8215415 B C P a b p f k x)). Qed.
Lemma lem8215418 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term92 B C P a k b p f x) = (term96 B C P a k b p f x).
Proof. exact (eq_refl (term92 B C P a k b p f x)). Qed.
Lemma lem8215419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8215420 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term95 B C P a k b p f x) = (term97 B C P a k b p f x).
Proof. exact (MK_COMB (@lem8215419) (@lem8215418 B C P a k b p f x)). Qed.
Lemma lem8215421 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term94 B C P a b p f k x) = (term94 B C P a b p f k x).
Proof. exact (eq_refl (term94 B C P a b p f k x)). Qed.
Lemma lem8215422 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p f x) = (term94 B C P a b p f k x)) = ((term96 B C P a k b p f x) = (term94 B C P a b p f k x)).
Proof. exact (MK_COMB (@lem8215420 B C P a k b p f x) (@lem8215421 B C P a b p f k x)). Qed.
Lemma lem8215423 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p f x) = (term93 B C P a b p f k x)) = ((term96 B C P a k b p f x) = (term94 B C P a b p f k x)).
Proof. exact (TRANS (@lem8215417 B C P a b p f k x) (@lem8215422 B C P a b p f k x)). Qed.
Lemma lem8215424 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term96 B C P a k b p f x) = (term94 B C P a b p f k x).
Proof. exact (EQ_MP (@lem8215423 B C P a b p f k x) (@lem8215414 B C P a b p f k x)). Qed.
Lemma lem8215425 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term94 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (SYM (@lem8215424 B C P a b p f k x)). Qed.
Lemma lem8215426 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) (x : P) : (term98 B C P a b p f k x) = (term94 B C P a b p f k x).
Proof. exact (eq_refl (term98 B C P a b p f k x)). Qed.
Lemma lem8215427 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term98 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (TRANS (@lem8215426 B C P a b p f k x) (@lem8215425 B C P a k b p f x)). Qed.
Lemma lem8215428 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term99 B C P a k b p f.
Proof. exact (fun x : P => @lem8215427 B C P a k b p f x). Qed.
Lemma lem8215429 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term100 B C P a b p f.
Proof. exact (fun k : nat => @lem8215428 B C P a k b p f). Qed.
Lemma lem8215430 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term101 B C P a b p f.
Proof. exact (ex_intro (term102 B C P a b p f) (term103 B C P a b p f) (@lem8215429 B C P a b p f)). Qed.
Lemma lem8215432 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8215433 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8215432 Prop a b). Qed.
Lemma lem8215434 {B C P : Type'} (_109147 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : ((term104 P _109147 k x) = (term96 B C P a k b p f x)) = (term105 B C P _109147 a k b p f x).
Proof. exact (@lem8215433 (term104 P _109147 k x) (term96 B C P a k b p f x)). Qed.
Lemma lem8215435 {B C P : Type'} (_109147 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term106 B C P _109147 a k b p f) = (term107 B C P _109147 a k b p f).
Proof. exact (fun_ext (fun x : P => @lem8215434 B C P _109147 a k b p f x)). Qed.
Lemma lem8215436 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8215437 {B C P : Type'} (_109147 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term108 B C P _109147 a k b p f) = (term109 B C P _109147 a k b p f).
Proof. exact (MK_COMB (@lem8215436 P) (@lem8215435 B C P _109147 a k b p f)). Qed.
Lemma lem8215438 {B C P : Type'} (_109147 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term110 B C P _109147 a b p f) = (term111 B C P _109147 a b p f).
Proof. exact (fun_ext (fun k : nat => @lem8215437 B C P _109147 a k b p f)). Qed.
Lemma lem8215439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8215440 {B C P : Type'} (_109147 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term112 B C P _109147 a b p f) = (term113 B C P _109147 a b p f).
Proof. exact (MK_COMB (@lem8215439) (@lem8215438 B C P _109147 a b p f)). Qed.
Lemma lem8215441 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term102 B C P a b p f) = (term114 B C P a b p f).
Proof. exact (fun_ext (fun _109147 : type1310 P => @lem8215440 B C P _109147 a b p f)). Qed.
Lemma lem8215442 {P : Type'} : (@ex ((prod nat P) -> Prop)) = (@ex ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat P) -> Prop))). Qed.
Lemma lem8215443 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term101 B C P a b p f) = (term115 B C P a b p f).
Proof. exact (MK_COMB (@lem8215442 P) (@lem8215441 B C P a b p f)). Qed.
Lemma lem8215444 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term115 B C P a b p f.
Proof. exact (EQ_MP (@lem8215443 B C P a b p f) (@lem8215430 B C P a b p f)). Qed.
Lemma lem8215446 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8215447 {P : Type'} (P' : type372 P) : term117 P P'.
Proof. exact (@lem8215446 (type1310 P) P'). Qed.
Lemma lem8215448 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term118 B C P a b p f.
Proof. exact (@lem8215447 P (term114 B C P a b p f)). Qed.
Lemma lem8215449 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term119 B C P a b p f.
Proof. exact (@lem8215448 B C P a b p f (@lem8215444 B C P a b p f)). Qed.
Lemma lem8215450 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term119 B C P a b p f) = (term120 B C P a b p f).
Proof. exact (eq_refl (term119 B C P a b p f)). Qed.
Lemma lem8215451 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term120 B C P a b p f.
Proof. exact (EQ_MP (@lem8215450 B C P a b p f) (@lem8215449 B C P a b p f)). Qed.
Lemma lem8215452 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (k : nat) : term121 B C P a b p f k.
Proof. exact (@lem8215451 B C P a b p f k). Qed.
Lemma lem8215453 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term121 B C P a b p f k) = (term122 B C P a k b p f).
Proof. exact (eq_refl (term121 B C P a b p f k)). Qed.
Lemma lem8215454 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : term122 B C P a k b p f.
Proof. exact (EQ_MP (@lem8215453 B C P a k b p f) (@lem8215452 B C P a b p f k)). Qed.
Lemma lem8215455 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : term123 B C P a k b p f x.
Proof. exact (@lem8215454 B C P a k b p f x). Qed.
Lemma lem8215456 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term123 B C P a k b p f x) = (term124 B C P a k b p f x).
Proof. exact (eq_refl (term123 B C P a k b p f x)). Qed.
Lemma lem8215457 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : term124 B C P a k b p f x.
Proof. exact (EQ_MP (@lem8215456 B C P a k b p f x) (@lem8215455 B C P a k b p f x)). Qed.
Lemma lem8215459 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8215460 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8215459 Prop a b). Qed.
Lemma lem8215461 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term124 B C P a k b p f x) = ((term74 B C P a b p f k x) = (term96 B C P a k b p f x)).
Proof. exact (@lem8215460 (term74 B C P a b p f k x) (term96 B C P a k b p f x)). Qed.
Lemma lem8215462 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term74 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (EQ_MP (@lem8215461 B C P a k b p f x) (@lem8215457 B C P a k b p f x)). Qed.
Lemma lem8215463 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (x : P) : (term74 B C P a b p f k x) = (term96 B C P a k b p f x).
Proof. exact (@lem8215462 B C P a k b p f x). Qed.
Lemma lem8215464 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term74 B C P a b p f p1 p2) = (term96 B C P a p1 b p f p2).
Proof. exact (@lem8215463 B C P a p1 b p f p2). Qed.
Lemma lem8215469 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term73 B C P a b p f p1 p2) = (term96 B C P a p1 b p f p2).
Proof. exact (TRANS (@lem8215365 B C P a b p f p1 p2) (@lem8215464 B C P a p1 b p f p2)). Qed.
Lemma lem8215470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8215471 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term125 B C P a b p f p1 p2) = (term126 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8215470) (@lem8215469 B C P a p1 b p f p2)). Qed.
Lemma lem8215475 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8215476 {B C P : Type'} (f : type542 B C P) (y : B -> C) : (term66 B C P f y) = (f y).
Proof. exact (@lem8215475 (B -> C) (type1310 P) f y). Qed.
Lemma lem8215477 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term67 B C P a b p g) = (term68 B C P a b p g).
Proof. exact (@lem8215476 B C P (term42 B C P a b p) g). Qed.
Lemma lem8215478 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) : (term68 B C P a b p f) = (term69 B C P a b p f).
Proof. exact (eq_refl (term68 B C P a b p f)). Qed.
Lemma lem8215479 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) : (term70 B C P a b p) = (term42 B C P a b p).
Proof. exact (fun_ext (fun f : B -> C => @lem8215478 B C P a b p f)). Qed.
Lemma lem8215480 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8215481 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term67 B C P a b p g) = (term68 B C P a b p g).
Proof. exact (MK_COMB (@lem8215479 B C P a b p) (@lem8215480 B C g)). Qed.
Lemma lem8215482 {P : Type'} : (@eq ((prod nat P) -> Prop)) = (@eq ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@eq ((prod nat P) -> Prop))). Qed.
Lemma lem8215483 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term71 B C P a b p g) = (term72 B C P a b p g).
Proof. exact (MK_COMB (@lem8215482 P) (@lem8215481 B C P a b p g)). Qed.
Lemma lem8215484 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term68 B C P a b p g) = (term69 B C P a b p g).
Proof. exact (eq_refl (term68 B C P a b p g)). Qed.
Lemma lem8215485 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term67 B C P a b p g) = (term68 B C P a b p g)) = ((term68 B C P a b p g) = (term69 B C P a b p g)).
Proof. exact (MK_COMB (@lem8215483 B C P a b p g) (@lem8215484 B C P a b p g)). Qed.
Lemma lem8215486 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term68 B C P a b p g) = (term69 B C P a b p g).
Proof. exact (EQ_MP (@lem8215485 B C P a b p g) (@lem8215477 B C P a b p g)). Qed.
Lemma lem8215503 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8215504 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p1 : nat) (p2 : P) : (term73 B C P a b p g p1 p2) = (term74 B C P a b p g p1 p2).
Proof. exact (MK_COMB (@lem8215486 B C P a b p g) (@lem8215503 P p1 p2)). Qed.
Lemma lem8215505 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8215506 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8215505 P k x). Qed.
Lemma lem8215507 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8215508 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8215507 P k x). Qed.
Lemma lem8215509 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8215510 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8215511 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8215510) (@lem8215506 P k x)). Qed.
Lemma lem8215512 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8215513 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8215514 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215513 k) (@lem8215512 P k x)). Qed.
Lemma lem8215515 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8215516 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215517 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8215516) (@lem8215515 k)). Qed.
Lemma lem8215518 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8215519 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215517 k) (@lem8215518 P k x)). Qed.
Lemma lem8215520 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8215514 P k x) (@lem8215519 P k x)). Qed.
Lemma lem8215521 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215520 P k x) (@lem8215511 P k x)). Qed.
Lemma lem8215522 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8215523 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215522 k) (@lem8215521 P k x)). Qed.
Lemma lem8215524 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215523 P k x) (@lem8215509 k)). Qed.
Lemma lem8215525 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8215526 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8215527 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8215526 P) (@lem8215508 P k x)). Qed.
Lemma lem8215528 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8215529 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8215530 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215529 P x) (@lem8215528 P k x)). Qed.
Lemma lem8215531 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8215532 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8215533 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8215532 P) (@lem8215531 P x)). Qed.
Lemma lem8215534 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8215535 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215533 P x) (@lem8215534 P k x)). Qed.
Lemma lem8215536 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8215530 P k x) (@lem8215535 P k x)). Qed.
Lemma lem8215537 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215536 P k x) (@lem8215527 P k x)). Qed.
Lemma lem8215538 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8215539 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215538 P x) (@lem8215537 P k x)). Qed.
Lemma lem8215540 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215539 P k x) (@lem8215525 P x)). Qed.
Lemma lem8215541 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term85 B C P a b p g) = (term85 B C P a b p g).
Proof. exact (eq_refl (term85 B C P a b p g)). Qed.
Lemma lem8215542 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term86 B C P a b p g k) = (term87 B C P a b p g k x).
Proof. exact (MK_COMB (@lem8215541 B C P a b p g) (@lem8215524 P k x)). Qed.
Lemma lem8215543 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term87 B C P a b p g k x) = (term88 B C P a k x b p g).
Proof. exact (eq_refl (term87 B C P a b p g k x)). Qed.
Lemma lem8215544 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) : (term89 B C P a b p g k) = (term89 B C P a b p g k).
Proof. exact (eq_refl (term89 B C P a b p g k)). Qed.
Lemma lem8215545 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term86 B C P a b p g k) = (term87 B C P a b p g k x)) = ((term86 B C P a b p g k) = (term88 B C P a k x b p g)).
Proof. exact (MK_COMB (@lem8215544 B C P a b p g k) (@lem8215543 B C P a k x b p g)). Qed.
Lemma lem8215546 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term86 B C P a b p g k) = (term90 B C P a k b p g).
Proof. exact (eq_refl (term86 B C P a b p g k)). Qed.
Lemma lem8215547 {P : Type'} : (@eq (P -> Prop)) = (@eq (P -> Prop)).
Proof. exact (eq_refl (@eq (P -> Prop))). Qed.
Lemma lem8215548 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term89 B C P a b p g k) = (term91 B C P a k b p g).
Proof. exact (MK_COMB (@lem8215547 P) (@lem8215546 B C P a k b p g)). Qed.
Lemma lem8215549 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term88 B C P a k x b p g) = (term88 B C P a k x b p g).
Proof. exact (eq_refl (term88 B C P a k x b p g)). Qed.
Lemma lem8215550 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term86 B C P a b p g k) = (term88 B C P a k x b p g)) = ((term90 B C P a k b p g) = (term88 B C P a k x b p g)).
Proof. exact (MK_COMB (@lem8215548 B C P a k b p g) (@lem8215549 B C P a k x b p g)). Qed.
Lemma lem8215551 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : ((term86 B C P a b p g k) = (term87 B C P a b p g k x)) = ((term90 B C P a k b p g) = (term88 B C P a k x b p g)).
Proof. exact (TRANS (@lem8215545 B C P a k x b p g) (@lem8215550 B C P a k x b p g)). Qed.
Lemma lem8215552 {B C P : Type'} (a : P -> nat) (k : nat) (x : P) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term90 B C P a k b p g) = (term88 B C P a k x b p g).
Proof. exact (EQ_MP (@lem8215551 B C P a k x b p g) (@lem8215542 B C P a b p g k x)). Qed.
Lemma lem8215553 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term92 B C P a k b p g x) = (term93 B C P a b p g k x).
Proof. exact (MK_COMB (@lem8215552 B C P a k x b p g) (@lem8215540 P k x)). Qed.
Lemma lem8215554 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term93 B C P a b p g k x) = (term94 B C P a b p g k x).
Proof. exact (eq_refl (term93 B C P a b p g k x)). Qed.
Lemma lem8215555 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term95 B C P a k b p g x) = (term95 B C P a k b p g x).
Proof. exact (eq_refl (term95 B C P a k b p g x)). Qed.
Lemma lem8215556 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p g x) = (term93 B C P a b p g k x)) = ((term92 B C P a k b p g x) = (term94 B C P a b p g k x)).
Proof. exact (MK_COMB (@lem8215555 B C P a k b p g x) (@lem8215554 B C P a b p g k x)). Qed.
Lemma lem8215557 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term92 B C P a k b p g x) = (term96 B C P a k b p g x).
Proof. exact (eq_refl (term92 B C P a k b p g x)). Qed.
Lemma lem8215558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8215559 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term95 B C P a k b p g x) = (term97 B C P a k b p g x).
Proof. exact (MK_COMB (@lem8215558) (@lem8215557 B C P a k b p g x)). Qed.
Lemma lem8215560 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term94 B C P a b p g k x) = (term94 B C P a b p g k x).
Proof. exact (eq_refl (term94 B C P a b p g k x)). Qed.
Lemma lem8215561 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p g x) = (term94 B C P a b p g k x)) = ((term96 B C P a k b p g x) = (term94 B C P a b p g k x)).
Proof. exact (MK_COMB (@lem8215559 B C P a k b p g x) (@lem8215560 B C P a b p g k x)). Qed.
Lemma lem8215562 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : ((term92 B C P a k b p g x) = (term93 B C P a b p g k x)) = ((term96 B C P a k b p g x) = (term94 B C P a b p g k x)).
Proof. exact (TRANS (@lem8215556 B C P a b p g k x) (@lem8215561 B C P a b p g k x)). Qed.
Lemma lem8215563 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term96 B C P a k b p g x) = (term94 B C P a b p g k x).
Proof. exact (EQ_MP (@lem8215562 B C P a b p g k x) (@lem8215553 B C P a b p g k x)). Qed.
Lemma lem8215564 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term94 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (SYM (@lem8215563 B C P a b p g k x)). Qed.
Lemma lem8215565 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) (x : P) : (term98 B C P a b p g k x) = (term94 B C P a b p g k x).
Proof. exact (eq_refl (term98 B C P a b p g k x)). Qed.
Lemma lem8215566 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term98 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (TRANS (@lem8215565 B C P a b p g k x) (@lem8215564 B C P a k b p g x)). Qed.
Lemma lem8215567 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term99 B C P a k b p g.
Proof. exact (fun x : P => @lem8215566 B C P a k b p g x). Qed.
Lemma lem8215568 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term100 B C P a b p g.
Proof. exact (fun k : nat => @lem8215567 B C P a k b p g). Qed.
Lemma lem8215569 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term101 B C P a b p g.
Proof. exact (ex_intro (term102 B C P a b p g) (term103 B C P a b p g) (@lem8215568 B C P a b p g)). Qed.
Lemma lem8215571 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8215572 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem8215571 Prop a b). Qed.
Lemma lem8215573 {B C P : Type'} (_109159 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : ((term104 P _109159 k x) = (term96 B C P a k b p g x)) = (term105 B C P _109159 a k b p g x).
Proof. exact (@lem8215572 (term104 P _109159 k x) (term96 B C P a k b p g x)). Qed.
Lemma lem8215574 {B C P : Type'} (_109159 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term106 B C P _109159 a k b p g) = (term107 B C P _109159 a k b p g).
Proof. exact (fun_ext (fun x : P => @lem8215573 B C P _109159 a k b p g x)). Qed.
Lemma lem8215575 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8215576 {B C P : Type'} (_109159 : type1310 P) (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term108 B C P _109159 a k b p g) = (term109 B C P _109159 a k b p g).
Proof. exact (MK_COMB (@lem8215575 P) (@lem8215574 B C P _109159 a k b p g)). Qed.
Lemma lem8215577 {B C P : Type'} (_109159 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term110 B C P _109159 a b p g) = (term111 B C P _109159 a b p g).
Proof. exact (fun_ext (fun k : nat => @lem8215576 B C P _109159 a k b p g)). Qed.
Lemma lem8215578 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8215579 {B C P : Type'} (_109159 : type1310 P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term112 B C P _109159 a b p g) = (term113 B C P _109159 a b p g).
Proof. exact (MK_COMB (@lem8215578) (@lem8215577 B C P _109159 a b p g)). Qed.
Lemma lem8215580 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term102 B C P a b p g) = (term114 B C P a b p g).
Proof. exact (fun_ext (fun _109159 : type1310 P => @lem8215579 B C P _109159 a b p g)). Qed.
Lemma lem8215581 {P : Type'} : (@ex ((prod nat P) -> Prop)) = (@ex ((prod nat P) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat P) -> Prop))). Qed.
Lemma lem8215582 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term101 B C P a b p g) = (term115 B C P a b p g).
Proof. exact (MK_COMB (@lem8215581 P) (@lem8215580 B C P a b p g)). Qed.
Lemma lem8215583 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term115 B C P a b p g.
Proof. exact (EQ_MP (@lem8215582 B C P a b p g) (@lem8215569 B C P a b p g)). Qed.
Lemma lem8215585 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8215586 {P : Type'} (P' : type372 P) : term117 P P'.
Proof. exact (@lem8215585 (type1310 P) P'). Qed.
Lemma lem8215587 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term118 B C P a b p g.
Proof. exact (@lem8215586 P (term114 B C P a b p g)). Qed.
Lemma lem8215588 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term119 B C P a b p g.
Proof. exact (@lem8215587 B C P a b p g (@lem8215583 B C P a b p g)). Qed.
Lemma lem8215589 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term119 B C P a b p g) = (term120 B C P a b p g).
Proof. exact (eq_refl (term119 B C P a b p g)). Qed.
Lemma lem8215590 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term120 B C P a b p g.
Proof. exact (EQ_MP (@lem8215589 B C P a b p g) (@lem8215588 B C P a b p g)). Qed.
Lemma lem8215591 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (k : nat) : term121 B C P a b p g k.
Proof. exact (@lem8215590 B C P a b p g k). Qed.
Lemma lem8215592 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : (term121 B C P a b p g k) = (term122 B C P a k b p g).
Proof. exact (eq_refl (term121 B C P a b p g k)). Qed.
Lemma lem8215593 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) : term122 B C P a k b p g.
Proof. exact (EQ_MP (@lem8215592 B C P a k b p g) (@lem8215591 B C P a b p g k)). Qed.
Lemma lem8215594 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : term123 B C P a k b p g x.
Proof. exact (@lem8215593 B C P a k b p g x). Qed.
Lemma lem8215595 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term123 B C P a k b p g x) = (term124 B C P a k b p g x).
Proof. exact (eq_refl (term123 B C P a k b p g x)). Qed.
Lemma lem8215596 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : term124 B C P a k b p g x.
Proof. exact (EQ_MP (@lem8215595 B C P a k b p g x) (@lem8215594 B C P a k b p g x)). Qed.
Lemma lem8215598 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8215599 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem8215598 Prop a b). Qed.
Lemma lem8215600 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term124 B C P a k b p g x) = ((term74 B C P a b p g k x) = (term96 B C P a k b p g x)).
Proof. exact (@lem8215599 (term74 B C P a b p g k x) (term96 B C P a k b p g x)). Qed.
Lemma lem8215601 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term74 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (EQ_MP (@lem8215600 B C P a k b p g x) (@lem8215596 B C P a k b p g x)). Qed.
Lemma lem8215602 {B C P : Type'} (a : P -> nat) (k : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (x : P) : (term74 B C P a b p g k x) = (term96 B C P a k b p g x).
Proof. exact (@lem8215601 B C P a k b p g x). Qed.
Lemma lem8215603 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term74 B C P a b p g p1 p2) = (term96 B C P a p1 b p g p2).
Proof. exact (@lem8215602 B C P a p1 b p g p2). Qed.
Lemma lem8215608 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term73 B C P a b p g p1 p2) = (term96 B C P a p1 b p g p2).
Proof. exact (TRANS (@lem8215504 B C P a b p g p1 p2) (@lem8215603 B C P a p1 b p g p2)). Qed.
Lemma lem8215609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8215610 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term125 B C P a b p g p1 p2) = (term126 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8215609) (@lem8215608 B C P a p1 b p g p2)). Qed.
Lemma lem8215619 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8215620 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8215619 P k x). Qed.
Lemma lem8215621 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8215622 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8215621 P k x). Qed.
Lemma lem8215623 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8215624 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8215625 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8215624) (@lem8215620 P k x)). Qed.
Lemma lem8215626 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8215627 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8215628 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215627 k) (@lem8215626 P k x)). Qed.
Lemma lem8215629 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8215630 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215631 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8215630) (@lem8215629 k)). Qed.
Lemma lem8215632 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8215633 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215631 k) (@lem8215632 P k x)). Qed.
Lemma lem8215634 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8215628 P k x) (@lem8215633 P k x)). Qed.
Lemma lem8215635 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215634 P k x) (@lem8215625 P k x)). Qed.
Lemma lem8215636 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8215637 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215636 k) (@lem8215635 P k x)). Qed.
Lemma lem8215638 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215637 P k x) (@lem8215623 k)). Qed.
Lemma lem8215639 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8215640 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8215641 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8215640 P) (@lem8215622 P k x)). Qed.
Lemma lem8215642 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8215643 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8215644 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215643 P x) (@lem8215642 P k x)). Qed.
Lemma lem8215645 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8215646 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8215647 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8215646 P) (@lem8215645 P x)). Qed.
Lemma lem8215648 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8215649 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215647 P x) (@lem8215648 P k x)). Qed.
Lemma lem8215650 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8215644 P k x) (@lem8215649 P k x)). Qed.
Lemma lem8215651 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215650 P k x) (@lem8215641 P k x)). Qed.
Lemma lem8215652 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8215653 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215652 P x) (@lem8215651 P k x)). Qed.
Lemma lem8215654 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215653 P k x) (@lem8215639 P x)). Qed.
Lemma lem8215655 {A P : Type'} (s : P -> A) : (term127 A P s) = (term127 A P s).
Proof. exact (eq_refl (term127 A P s)). Qed.
Lemma lem8215656 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term128 A P s k) = (term129 A P s k x).
Proof. exact (MK_COMB (@lem8215655 A P s) (@lem8215638 P k x)). Qed.
Lemma lem8215657 {A P : Type'} (k : nat) (x : P) (s : P -> A) : (term129 A P s k x) = (term130 A P s).
Proof. exact (eq_refl (term129 A P s k x)). Qed.
Lemma lem8215658 {A P : Type'} (s : P -> A) (k : nat) : (term131 A P s k) = (term131 A P s k).
Proof. exact (eq_refl (term131 A P s k)). Qed.
Lemma lem8215659 {A P : Type'} (x : P) (k : nat) (s : P -> A) : ((term128 A P s k) = (term129 A P s k x)) = ((term128 A P s k) = (term130 A P s)).
Proof. exact (MK_COMB (@lem8215658 A P s k) (@lem8215657 A P k x s)). Qed.
Lemma lem8215660 {A P : Type'} (k : nat) (s : P -> A) : (term128 A P s k) = (term130 A P s).
Proof. exact (eq_refl (term128 A P s k)). Qed.
Lemma lem8215661 {A P : Type'} : (@eq (P -> A)) = (@eq (P -> A)).
Proof. exact (eq_refl (@eq (P -> A))). Qed.
Lemma lem8215662 {A P : Type'} (k : nat) (s : P -> A) : (term131 A P s k) = (term132 A P s).
Proof. exact (MK_COMB (@lem8215661 A P) (@lem8215660 A P k s)). Qed.
Lemma lem8215663 {A P : Type'} (s : P -> A) : (term130 A P s) = (term130 A P s).
Proof. exact (eq_refl (term130 A P s)). Qed.
Lemma lem8215664 {A P : Type'} (k : nat) (s : P -> A) : ((term128 A P s k) = (term130 A P s)) = ((term130 A P s) = (term130 A P s)).
Proof. exact (MK_COMB (@lem8215662 A P k s) (@lem8215663 A P s)). Qed.
Lemma lem8215665 {A P : Type'} (k : nat) (x : P) (s : P -> A) : ((term128 A P s k) = (term129 A P s k x)) = ((term130 A P s) = (term130 A P s)).
Proof. exact (TRANS (@lem8215659 A P x k s) (@lem8215664 A P k s)). Qed.
Lemma lem8215666 {A P : Type'} (s : P -> A) : (term130 A P s) = (term130 A P s).
Proof. exact (EQ_MP (@lem8215665 A P (@el nat) (@el P) s) (@lem8215656 A P s (@el nat) (@el P))). Qed.
Lemma lem8215667 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term133 A P s x) = (term134 A P s k x).
Proof. exact (MK_COMB (@lem8215666 A P s) (@lem8215654 P k x)). Qed.
Lemma lem8215668 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term134 A P s k x) = (term135 A P s k x).
Proof. exact (eq_refl (term134 A P s k x)). Qed.
Lemma lem8215669 {A P : Type'} (s : P -> A) (x : P) : (term136 A P s x) = (term136 A P s x).
Proof. exact (eq_refl (term136 A P s x)). Qed.
Lemma lem8215670 {A P : Type'} (s : P -> A) (k : nat) (x : P) : ((term133 A P s x) = (term134 A P s k x)) = ((term133 A P s x) = (term135 A P s k x)).
Proof. exact (MK_COMB (@lem8215669 A P s x) (@lem8215668 A P s k x)). Qed.
Lemma lem8215671 {A P : Type'} (s : P -> A) (x : P) : (term133 A P s x) = (s x).
Proof. exact (eq_refl (term133 A P s x)). Qed.
Lemma lem8215672 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem8215673 {A P : Type'} (s : P -> A) (x : P) : (term136 A P s x) = (term137 A P s x).
Proof. exact (MK_COMB (@lem8215672 A) (@lem8215671 A P s x)). Qed.
Lemma lem8215674 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term135 A P s k x) = (term135 A P s k x).
Proof. exact (eq_refl (term135 A P s k x)). Qed.
Lemma lem8215675 {A P : Type'} (s : P -> A) (k : nat) (x : P) : ((term133 A P s x) = (term135 A P s k x)) = ((s x) = (term135 A P s k x)).
Proof. exact (MK_COMB (@lem8215673 A P s x) (@lem8215674 A P s k x)). Qed.
Lemma lem8215676 {A P : Type'} (s : P -> A) (k : nat) (x : P) : ((term133 A P s x) = (term134 A P s k x)) = ((s x) = (term135 A P s k x)).
Proof. exact (TRANS (@lem8215670 A P s k x) (@lem8215675 A P s k x)). Qed.
Lemma lem8215677 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (s x) = (term135 A P s k x).
Proof. exact (EQ_MP (@lem8215676 A P s k x) (@lem8215667 A P s k x)). Qed.
Lemma lem8215678 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term135 A P s k x) = (s x).
Proof. exact (SYM (@lem8215677 A P s k x)). Qed.
Lemma lem8215679 {A P : Type'} (s : P -> A) (k : nat) (x : P) : (term138 A P s k x) = (term135 A P s k x).
Proof. exact (eq_refl (term138 A P s k x)). Qed.
Lemma lem8215680 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term138 A P s k x) = (s x).
Proof. exact (TRANS (@lem8215679 A P s k x) (@lem8215678 A P k s x)). Qed.
Lemma lem8215681 {A P : Type'} (k : nat) (s : P -> A) : term139 A P k s.
Proof. exact (fun x : P => @lem8215680 A P k s x). Qed.
Lemma lem8215682 {A P : Type'} (s : P -> A) : term140 A P s.
Proof. exact (fun k : nat => @lem8215681 A P k s). Qed.
Lemma lem8215683 {A P : Type'} (s : P -> A) : term141 A P s.
Proof. exact (ex_intro (term142 A P s) (term143 A P s) (@lem8215682 A P s)). Qed.
Lemma lem8215685 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8215686 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (@lem8215685 A a b). Qed.
Lemma lem8215687 {A P : Type'} (_109171 : type1313 A P) (k : nat) (s : P -> A) (x : P) : ((term144 A P _109171 k x) = (s x)) = (term145 A P _109171 k s x).
Proof. exact (@lem8215686 A (term144 A P _109171 k x) (s x)). Qed.
Lemma lem8215688 {A P : Type'} (_109171 : type1313 A P) (k : nat) (s : P -> A) : (term146 A P _109171 k s) = (term147 A P _109171 k s).
Proof. exact (fun_ext (fun x : P => @lem8215687 A P _109171 k s x)). Qed.
Lemma lem8215689 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8215690 {A P : Type'} (_109171 : type1313 A P) (k : nat) (s : P -> A) : (term148 A P _109171 k s) = (term149 A P _109171 k s).
Proof. exact (MK_COMB (@lem8215689 P) (@lem8215688 A P _109171 k s)). Qed.
Lemma lem8215691 {A P : Type'} (_109171 : type1313 A P) (s : P -> A) : (term150 A P _109171 s) = (term151 A P _109171 s).
Proof. exact (fun_ext (fun k : nat => @lem8215690 A P _109171 k s)). Qed.
Lemma lem8215692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8215693 {A P : Type'} (_109171 : type1313 A P) (s : P -> A) : (term152 A P _109171 s) = (term153 A P _109171 s).
Proof. exact (MK_COMB (@lem8215692) (@lem8215691 A P _109171 s)). Qed.
Lemma lem8215694 {A P : Type'} (s : P -> A) : (term142 A P s) = (term154 A P s).
Proof. exact (fun_ext (fun _109171 : type1313 A P => @lem8215693 A P _109171 s)). Qed.
Lemma lem8215695 {A P : Type'} : (@ex ((prod nat P) -> A)) = (@ex ((prod nat P) -> A)).
Proof. exact (eq_refl (@ex ((prod nat P) -> A))). Qed.
Lemma lem8215696 {A P : Type'} (s : P -> A) : (term141 A P s) = (term155 A P s).
Proof. exact (MK_COMB (@lem8215695 A P) (@lem8215694 A P s)). Qed.
Lemma lem8215697 {A P : Type'} (s : P -> A) : term155 A P s.
Proof. exact (EQ_MP (@lem8215696 A P s) (@lem8215683 A P s)). Qed.
Lemma lem8215699 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8215700 {A P : Type'} (P' : type375 A P) : term156 A P P'.
Proof. exact (@lem8215699 (type1313 A P) P'). Qed.
Lemma lem8215701 {A P : Type'} (s : P -> A) : term157 A P s.
Proof. exact (@lem8215700 A P (term154 A P s)). Qed.
Lemma lem8215702 {A P : Type'} (s : P -> A) : term158 A P s.
Proof. exact (@lem8215701 A P s (@lem8215697 A P s)). Qed.
Lemma lem8215703 {A P : Type'} (s : P -> A) : (term158 A P s) = (term159 A P s).
Proof. exact (eq_refl (term158 A P s)). Qed.
Lemma lem8215704 {A P : Type'} (s : P -> A) : term159 A P s.
Proof. exact (EQ_MP (@lem8215703 A P s) (@lem8215702 A P s)). Qed.
Lemma lem8215705 {A P : Type'} (s : P -> A) (k : nat) : term160 A P s k.
Proof. exact (@lem8215704 A P s k). Qed.
Lemma lem8215706 {A P : Type'} (k : nat) (s : P -> A) : (term160 A P s k) = (term161 A P k s).
Proof. exact (eq_refl (term160 A P s k)). Qed.
Lemma lem8215707 {A P : Type'} (k : nat) (s : P -> A) : term161 A P k s.
Proof. exact (EQ_MP (@lem8215706 A P k s) (@lem8215705 A P s k)). Qed.
Lemma lem8215708 {A P : Type'} (k : nat) (s : P -> A) (x : P) : term162 A P k s x.
Proof. exact (@lem8215707 A P k s x). Qed.
Lemma lem8215709 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term162 A P k s x) = (term163 A P k s x).
Proof. exact (eq_refl (term162 A P k s x)). Qed.
Lemma lem8215710 {A P : Type'} (k : nat) (s : P -> A) (x : P) : term163 A P k s x.
Proof. exact (EQ_MP (@lem8215709 A P k s x) (@lem8215708 A P k s x)). Qed.
Lemma lem8215712 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8215713 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (@lem8215712 A a b). Qed.
Lemma lem8215714 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term163 A P k s x) = ((term164 A P s k x) = (s x)).
Proof. exact (@lem8215713 A (term164 A P s k x) (s x)). Qed.
Lemma lem8215715 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term164 A P s k x) = (s x).
Proof. exact (EQ_MP (@lem8215714 A P k s x) (@lem8215710 A P k s x)). Qed.
Lemma lem8215716 {A P : Type'} (k : nat) (s : P -> A) (x : P) : (term164 A P s k x) = (s x).
Proof. exact (@lem8215715 A P k s x). Qed.
Lemma lem8215717 {A P : Type'} (p1 : nat) (s : P -> A) (p2 : P) : (term164 A P s p1 p2) = (s p2).
Proof. exact (@lem8215716 A P p1 s p2). Qed.
Lemma lem8215718 {A B : Type'} (lt2 : type1470 A B) (z : B) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8215719 {A B P : Type'} (p1 : nat) (lt2 : type1470 A B) (z : B) (s : P -> A) (p2 : P) : (term165 A B P lt2 z s p1 p2) = (term166 A B P lt2 z s p2).
Proof. exact (MK_COMB (@lem8215718 A B lt2 z) (@lem8215717 A P p1 s p2)). Qed.
Lemma lem8215720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8215721 {A B P : Type'} (p1 : nat) (lt2 : type1470 A B) (z : B) (s : P -> A) (p2 : P) : (term167 A B P lt2 z s p1 p2) = (term168 A B P lt2 z s p2).
Proof. exact (MK_COMB (@lem8215720) (@lem8215719 A B P p1 lt2 z s p2)). Qed.
Lemma lem8215724 {B C : Type'} (f : B -> C) (g : B -> C) (z : B) : ((f z) = (g z)) = ((f z) = (g z)).
Proof. exact (eq_refl ((f z) = (g z))). Qed.
Lemma lem8215725 {A B C P : Type'} (p1 : nat) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term169 A B C P lt2 s p1 p2 f g z) = (term170 A B C P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8215721 A B P p1 lt2 z s p2) (@lem8215724 B C f g z)). Qed.
Lemma lem8215728 {A B C P : Type'} (p1 : nat) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term171 A B C P lt2 s p1 p2 f g) = (term172 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8215725 A B C P p1 lt2 s p2 f g z)). Qed.
Lemma lem8215729 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8215730 {A B C P : Type'} (p1 : nat) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term173 A B C P lt2 s p1 p2 f g) = (term174 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8215729 B) (@lem8215728 A B C P p1 lt2 s p2 f g)). Qed.
Lemma lem8215737 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term175 A B C P a b p lt2 s p1 p2 f g) = (term176 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8215610 B C P a p1 b p g p2) (@lem8215730 A B C P p1 lt2 s p2 f g)). Qed.
Lemma lem8215740 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term177 A B C P a b p lt2 s p1 p2 f g) = (term178 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8215471 B C P a p1 b p f p2) (@lem8215737 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8215743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8215744 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term179 A B C P a b p lt2 s p1 p2 f g) = (term180 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8215743) (@lem8215740 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8215748 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8215749 {B C P : Type'} (f : type543 B C P) (y : B -> C) : (term181 B C P f y) = (f y).
Proof. exact (@lem8215748 (B -> C) (type1311 P) f y). Qed.
Lemma lem8215750 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term182 B C P h f) = (term183 B C P h f).
Proof. exact (@lem8215749 B C P (term44 B C P h) f). Qed.
Lemma lem8215751 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (eq_refl (term183 B C P h f)). Qed.
Lemma lem8215752 {B C P : Type'} (h : type555 B C P) : (term185 B C P h) = (term44 B C P h).
Proof. exact (fun_ext (fun f : B -> C => @lem8215751 B C P h f)). Qed.
Lemma lem8215753 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8215754 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term182 B C P h f) = (term183 B C P h f).
Proof. exact (MK_COMB (@lem8215752 B C P h) (@lem8215753 B C f)). Qed.
Lemma lem8215755 {P : Type'} : (@eq ((prod nat P) -> nat)) = (@eq ((prod nat P) -> nat)).
Proof. exact (eq_refl (@eq ((prod nat P) -> nat))). Qed.
Lemma lem8215756 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term186 B C P h f) = (term187 B C P h f).
Proof. exact (MK_COMB (@lem8215755 P) (@lem8215754 B C P h f)). Qed.
Lemma lem8215757 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (eq_refl (term183 B C P h f)). Qed.
Lemma lem8215758 {B C P : Type'} (h : type555 B C P) (f : B -> C) : ((term182 B C P h f) = (term183 B C P h f)) = ((term183 B C P h f) = (term184 B C P h f)).
Proof. exact (MK_COMB (@lem8215756 B C P h f) (@lem8215757 B C P h f)). Qed.
Lemma lem8215759 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (EQ_MP (@lem8215758 B C P h f) (@lem8215750 B C P h f)). Qed.
Lemma lem8215772 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8215773 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p1 : nat) (p2 : P) : (term188 B C P h f p1 p2) = (term189 B C P h f p1 p2).
Proof. exact (MK_COMB (@lem8215759 B C P h f) (@lem8215772 P p1 p2)). Qed.
Lemma lem8215774 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8215775 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8215774 P k x). Qed.
Lemma lem8215776 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8215777 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8215776 P k x). Qed.
Lemma lem8215778 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8215779 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8215780 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8215779) (@lem8215775 P k x)). Qed.
Lemma lem8215781 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8215782 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8215783 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215782 k) (@lem8215781 P k x)). Qed.
Lemma lem8215784 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8215785 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215786 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8215785) (@lem8215784 k)). Qed.
Lemma lem8215787 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8215788 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215786 k) (@lem8215787 P k x)). Qed.
Lemma lem8215789 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8215783 P k x) (@lem8215788 P k x)). Qed.
Lemma lem8215790 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215789 P k x) (@lem8215780 P k x)). Qed.
Lemma lem8215791 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8215792 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215791 k) (@lem8215790 P k x)). Qed.
Lemma lem8215793 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215792 P k x) (@lem8215778 k)). Qed.
Lemma lem8215794 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8215795 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8215796 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8215795 P) (@lem8215777 P k x)). Qed.
Lemma lem8215797 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8215798 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8215799 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215798 P x) (@lem8215797 P k x)). Qed.
Lemma lem8215800 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8215801 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8215802 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8215801 P) (@lem8215800 P x)). Qed.
Lemma lem8215803 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8215804 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215802 P x) (@lem8215803 P k x)). Qed.
Lemma lem8215805 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8215799 P k x) (@lem8215804 P k x)). Qed.
Lemma lem8215806 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215805 P k x) (@lem8215796 P k x)). Qed.
Lemma lem8215807 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8215808 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215807 P x) (@lem8215806 P k x)). Qed.
Lemma lem8215809 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215808 P k x) (@lem8215794 P x)). Qed.
Lemma lem8215810 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term190 B C P h f) = (term190 B C P h f).
Proof. exact (eq_refl (term190 B C P h f)). Qed.
Lemma lem8215811 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term191 B C P h f k) = (term192 B C P h f k x).
Proof. exact (MK_COMB (@lem8215810 B C P h f) (@lem8215793 P k x)). Qed.
Lemma lem8215812 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term192 B C P h f k x) = (term193 B C P h f k x).
Proof. exact (eq_refl (term192 B C P h f k x)). Qed.
Lemma lem8215813 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) : (term194 B C P h f k) = (term194 B C P h f k).
Proof. exact (eq_refl (term194 B C P h f k)). Qed.
Lemma lem8215814 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : ((term191 B C P h f k) = (term192 B C P h f k x)) = ((term191 B C P h f k) = (term193 B C P h f k x)).
Proof. exact (MK_COMB (@lem8215813 B C P h f k) (@lem8215812 B C P h f k x)). Qed.
Lemma lem8215815 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) : (term191 B C P h f k) = (term195 B C P h f k).
Proof. exact (eq_refl (term191 B C P h f k)). Qed.
Lemma lem8215816 {P : Type'} : (@eq (P -> nat)) = (@eq (P -> nat)).
Proof. exact (eq_refl (@eq (P -> nat))). Qed.
Lemma lem8215817 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) : (term194 B C P h f k) = (term196 B C P h f k).
Proof. exact (MK_COMB (@lem8215816 P) (@lem8215815 B C P h f k)). Qed.
Lemma lem8215818 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term193 B C P h f k x) = (term193 B C P h f k x).
Proof. exact (eq_refl (term193 B C P h f k x)). Qed.
Lemma lem8215819 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : ((term191 B C P h f k) = (term193 B C P h f k x)) = ((term195 B C P h f k) = (term193 B C P h f k x)).
Proof. exact (MK_COMB (@lem8215817 B C P h f k) (@lem8215818 B C P h f k x)). Qed.
Lemma lem8215820 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : ((term191 B C P h f k) = (term192 B C P h f k x)) = ((term195 B C P h f k) = (term193 B C P h f k x)).
Proof. exact (TRANS (@lem8215814 B C P h f k x) (@lem8215819 B C P h f k x)). Qed.
Lemma lem8215821 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term195 B C P h f k) = (term193 B C P h f k x).
Proof. exact (EQ_MP (@lem8215820 B C P h f k x) (@lem8215811 B C P h f k x)). Qed.
Lemma lem8215822 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term197 B C P h f k x) = (term198 B C P h f k x).
Proof. exact (MK_COMB (@lem8215821 B C P h f k x) (@lem8215809 P k x)). Qed.
Lemma lem8215823 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term198 B C P h f k x) = (term199 B C P h f k x).
Proof. exact (eq_refl (term198 B C P h f k x)). Qed.
Lemma lem8215824 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term200 B C P h f k x) = (term200 B C P h f k x).
Proof. exact (eq_refl (term200 B C P h f k x)). Qed.
Lemma lem8215825 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : ((term197 B C P h f k x) = (term198 B C P h f k x)) = ((term197 B C P h f k x) = (term199 B C P h f k x)).
Proof. exact (MK_COMB (@lem8215824 B C P h f k x) (@lem8215823 B C P h f k x)). Qed.
Lemma lem8215826 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term197 B C P h f k x) = (h f x k).
Proof. exact (eq_refl (term197 B C P h f k x)). Qed.
Lemma lem8215827 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215828 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term200 B C P h f k x) = (term201 B C P h f x k).
Proof. exact (MK_COMB (@lem8215827) (@lem8215826 B C P h f x k)). Qed.
Lemma lem8215829 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term199 B C P h f k x) = (term199 B C P h f k x).
Proof. exact (eq_refl (term199 B C P h f k x)). Qed.
Lemma lem8215830 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : ((term197 B C P h f k x) = (term199 B C P h f k x)) = ((h f x k) = (term199 B C P h f k x)).
Proof. exact (MK_COMB (@lem8215828 B C P h f x k) (@lem8215829 B C P h f k x)). Qed.
Lemma lem8215831 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : ((term197 B C P h f k x) = (term198 B C P h f k x)) = ((h f x k) = (term199 B C P h f k x)).
Proof. exact (TRANS (@lem8215825 B C P h f k x) (@lem8215830 B C P h f k x)). Qed.
Lemma lem8215832 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (h f x k) = (term199 B C P h f k x).
Proof. exact (EQ_MP (@lem8215831 B C P h f k x) (@lem8215822 B C P h f k x)). Qed.
Lemma lem8215833 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term199 B C P h f k x) = (h f x k).
Proof. exact (SYM (@lem8215832 B C P h f k x)). Qed.
Lemma lem8215834 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : (term202 B C P h f k x) = (term199 B C P h f k x).
Proof. exact (eq_refl (term202 B C P h f k x)). Qed.
Lemma lem8215835 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term202 B C P h f k x) = (h f x k).
Proof. exact (TRANS (@lem8215834 B C P h f k x) (@lem8215833 B C P h f x k)). Qed.
Lemma lem8215836 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) : term203 B C P h f k.
Proof. exact (fun x : P => @lem8215835 B C P h f x k). Qed.
Lemma lem8215837 {B C P : Type'} (h : type555 B C P) (f : B -> C) : term204 B C P h f.
Proof. exact (fun k : nat => @lem8215836 B C P h f k). Qed.
Lemma lem8215838 {B C P : Type'} (h : type555 B C P) (f : B -> C) : term205 B C P h f.
Proof. exact (ex_intro (term206 B C P h f) (term207 B C P h f) (@lem8215837 B C P h f)). Qed.
Lemma lem8215840 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8215841 (a : nat) (b : nat) : (a = b) = (@GEQ nat a b).
Proof. exact (@lem8215840 nat a b). Qed.
Lemma lem8215842 {B C P : Type'} (_109183 : type1311 P) (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : ((term208 P _109183 k x) = (h f x k)) = (term209 B C P _109183 h f x k).
Proof. exact (@lem8215841 (term208 P _109183 k x) (h f x k)). Qed.
Lemma lem8215843 {B C P : Type'} (_109183 : type1311 P) (h : type555 B C P) (f : B -> C) (k : nat) : (term210 B C P _109183 h f k) = (term211 B C P _109183 h f k).
Proof. exact (fun_ext (fun x : P => @lem8215842 B C P _109183 h f x k)). Qed.
Lemma lem8215844 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8215845 {B C P : Type'} (_109183 : type1311 P) (h : type555 B C P) (f : B -> C) (k : nat) : (term212 B C P _109183 h f k) = (term213 B C P _109183 h f k).
Proof. exact (MK_COMB (@lem8215844 P) (@lem8215843 B C P _109183 h f k)). Qed.
Lemma lem8215846 {B C P : Type'} (_109183 : type1311 P) (h : type555 B C P) (f : B -> C) : (term214 B C P _109183 h f) = (term215 B C P _109183 h f).
Proof. exact (fun_ext (fun k : nat => @lem8215845 B C P _109183 h f k)). Qed.
Lemma lem8215847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8215848 {B C P : Type'} (_109183 : type1311 P) (h : type555 B C P) (f : B -> C) : (term216 B C P _109183 h f) = (term217 B C P _109183 h f).
Proof. exact (MK_COMB (@lem8215847) (@lem8215846 B C P _109183 h f)). Qed.
Lemma lem8215849 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term206 B C P h f) = (term218 B C P h f).
Proof. exact (fun_ext (fun _109183 : type1311 P => @lem8215848 B C P _109183 h f)). Qed.
Lemma lem8215850 {P : Type'} : (@ex ((prod nat P) -> nat)) = (@ex ((prod nat P) -> nat)).
Proof. exact (eq_refl (@ex ((prod nat P) -> nat))). Qed.
Lemma lem8215851 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term205 B C P h f) = (term219 B C P h f).
Proof. exact (MK_COMB (@lem8215850 P) (@lem8215849 B C P h f)). Qed.
Lemma lem8215852 {B C P : Type'} (h : type555 B C P) (f : B -> C) : term219 B C P h f.
Proof. exact (EQ_MP (@lem8215851 B C P h f) (@lem8215838 B C P h f)). Qed.
Lemma lem8215854 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8215855 {P : Type'} (P' : type373 P) : term220 P P'.
Proof. exact (@lem8215854 (type1311 P) P'). Qed.
Lemma lem8215856 {B C P : Type'} (h : type555 B C P) (f : B -> C) : term221 B C P h f.
Proof. exact (@lem8215855 P (term218 B C P h f)). Qed.
Lemma lem8215857 {B C P : Type'} (h : type555 B C P) (f : B -> C) : term222 B C P h f.
Proof. exact (@lem8215856 B C P h f (@lem8215852 B C P h f)). Qed.
Lemma lem8215858 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term222 B C P h f) = (term223 B C P h f).
Proof. exact (eq_refl (term222 B C P h f)). Qed.
Lemma lem8215859 {B C P : Type'} (h : type555 B C P) (f : B -> C) : term223 B C P h f.
Proof. exact (EQ_MP (@lem8215858 B C P h f) (@lem8215857 B C P h f)). Qed.
Lemma lem8215860 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) : term224 B C P h f k.
Proof. exact (@lem8215859 B C P h f k). Qed.
Lemma lem8215861 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) : (term224 B C P h f k) = (term225 B C P h f k).
Proof. exact (eq_refl (term224 B C P h f k)). Qed.
Lemma lem8215862 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) : term225 B C P h f k.
Proof. exact (EQ_MP (@lem8215861 B C P h f k) (@lem8215860 B C P h f k)). Qed.
Lemma lem8215863 {B C P : Type'} (h : type555 B C P) (f : B -> C) (k : nat) (x : P) : term226 B C P h f k x.
Proof. exact (@lem8215862 B C P h f k x). Qed.
Lemma lem8215864 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term226 B C P h f k x) = (term227 B C P h f x k).
Proof. exact (eq_refl (term226 B C P h f k x)). Qed.
Lemma lem8215865 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : term227 B C P h f x k.
Proof. exact (EQ_MP (@lem8215864 B C P h f x k) (@lem8215863 B C P h f k x)). Qed.
Lemma lem8215867 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8215868 (a : nat) (b : nat) : (@GEQ nat a b) = (a = b).
Proof. exact (@lem8215867 nat a b). Qed.
Lemma lem8215869 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term227 B C P h f x k) = ((term189 B C P h f k x) = (h f x k)).
Proof. exact (@lem8215868 (term189 B C P h f k x) (h f x k)). Qed.
Lemma lem8215870 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term189 B C P h f k x) = (h f x k).
Proof. exact (EQ_MP (@lem8215869 B C P h f x k) (@lem8215865 B C P h f x k)). Qed.
Lemma lem8215871 {B C P : Type'} (h : type555 B C P) (f : B -> C) (x : P) (k : nat) : (term189 B C P h f k x) = (h f x k).
Proof. exact (@lem8215870 B C P h f x k). Qed.
Lemma lem8215872 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term189 B C P h f p1 p2) = (h f p2 p1).
Proof. exact (@lem8215871 B C P h f p2 p1). Qed.
Lemma lem8215873 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term188 B C P h f p1 p2) = (h f p2 p1).
Proof. exact (TRANS (@lem8215773 B C P h f p1 p2) (@lem8215872 B C P h f p2 p1)). Qed.
Lemma lem8215874 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215875 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term228 B C P h f p1 p2) = (term201 B C P h f p2 p1).
Proof. exact (MK_COMB (@lem8215874) (@lem8215873 B C P h f p2 p1)). Qed.
Lemma lem8215877 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8215878 {B C P : Type'} (f : type543 B C P) (y : B -> C) : (term181 B C P f y) = (f y).
Proof. exact (@lem8215877 (B -> C) (type1311 P) f y). Qed.
Lemma lem8215879 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term182 B C P h g) = (term183 B C P h g).
Proof. exact (@lem8215878 B C P (term44 B C P h) g). Qed.
Lemma lem8215880 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (term183 B C P h f) = (term184 B C P h f).
Proof. exact (eq_refl (term183 B C P h f)). Qed.
Lemma lem8215881 {B C P : Type'} (h : type555 B C P) : (term185 B C P h) = (term44 B C P h).
Proof. exact (fun_ext (fun f : B -> C => @lem8215880 B C P h f)). Qed.
Lemma lem8215882 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8215883 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term182 B C P h g) = (term183 B C P h g).
Proof. exact (MK_COMB (@lem8215881 B C P h) (@lem8215882 B C g)). Qed.
Lemma lem8215884 {P : Type'} : (@eq ((prod nat P) -> nat)) = (@eq ((prod nat P) -> nat)).
Proof. exact (eq_refl (@eq ((prod nat P) -> nat))). Qed.
Lemma lem8215885 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term186 B C P h g) = (term187 B C P h g).
Proof. exact (MK_COMB (@lem8215884 P) (@lem8215883 B C P h g)). Qed.
Lemma lem8215886 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term183 B C P h g) = (term184 B C P h g).
Proof. exact (eq_refl (term183 B C P h g)). Qed.
Lemma lem8215887 {B C P : Type'} (h : type555 B C P) (g : B -> C) : ((term182 B C P h g) = (term183 B C P h g)) = ((term183 B C P h g) = (term184 B C P h g)).
Proof. exact (MK_COMB (@lem8215885 B C P h g) (@lem8215886 B C P h g)). Qed.
Lemma lem8215888 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term183 B C P h g) = (term184 B C P h g).
Proof. exact (EQ_MP (@lem8215887 B C P h g) (@lem8215879 B C P h g)). Qed.
Lemma lem8215901 {P : Type'} (p1 : nat) (p2 : P) : (@pair nat P p1 p2) = (@pair nat P p1 p2).
Proof. exact (eq_refl (@pair nat P p1 p2)). Qed.
Lemma lem8215902 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p1 : nat) (p2 : P) : (term188 B C P h g p1 p2) = (term189 B C P h g p1 p2).
Proof. exact (MK_COMB (@lem8215888 B C P h g) (@lem8215901 P p1 p2)). Qed.
Lemma lem8215903 {P : Type'} (a0 : nat) (a1 : P) : a0 = (term75 P a0 a1).
Proof. exact (@lem51128 nat P a0 a1). Qed.
Lemma lem8215904 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (@lem8215903 P k x). Qed.
Lemma lem8215905 {P : Type'} (a0 : nat) (a1 : P) : a1 = (term76 P a0 a1).
Proof. exact (@lem51159 nat P a0 a1). Qed.
Lemma lem8215906 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (@lem8215905 P k x). Qed.
Lemma lem8215907 (k : nat) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem8215908 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem8215909 {P : Type'} (k : nat) (x : P) : (term78 k) = (term79 P k x).
Proof. exact (MK_COMB (@lem8215908) (@lem8215904 P k x)). Qed.
Lemma lem8215910 {P : Type'} (k : nat) (x : P) : (term79 P k x) = (term75 P k x).
Proof. exact (eq_refl (term79 P k x)). Qed.
Lemma lem8215911 (k : nat) : (term80 k) = (term80 k).
Proof. exact (eq_refl (term80 k)). Qed.
Lemma lem8215912 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = ((term78 k) = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215911 k) (@lem8215910 P k x)). Qed.
Lemma lem8215913 (k : nat) : (term78 k) = k.
Proof. exact (eq_refl (term78 k)). Qed.
Lemma lem8215914 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215915 (k : nat) : (term80 k) = (@eq nat k).
Proof. exact (MK_COMB (@lem8215914) (@lem8215913 k)). Qed.
Lemma lem8215916 {P : Type'} (k : nat) (x : P) : (term75 P k x) = (term75 P k x).
Proof. exact (eq_refl (term75 P k x)). Qed.
Lemma lem8215917 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term75 P k x)) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215915 k) (@lem8215916 P k x)). Qed.
Lemma lem8215918 {P : Type'} (k : nat) (x : P) : ((term78 k) = (term79 P k x)) = (k = (term75 P k x)).
Proof. exact (TRANS (@lem8215912 P k x) (@lem8215917 P k x)). Qed.
Lemma lem8215919 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215918 P k x) (@lem8215909 P k x)). Qed.
Lemma lem8215920 (k : nat) : (@eq nat k) = (@eq nat k).
Proof. exact (eq_refl (@eq nat k)). Qed.
Lemma lem8215921 {P : Type'} (k : nat) (x : P) : (k = k) = (k = (term75 P k x)).
Proof. exact (MK_COMB (@lem8215920 k) (@lem8215919 P k x)). Qed.
Lemma lem8215922 {P : Type'} (k : nat) (x : P) : k = (term75 P k x).
Proof. exact (EQ_MP (@lem8215921 P k x) (@lem8215907 k)). Qed.
Lemma lem8215923 {P : Type'} (x : P) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem8215924 {P : Type'} : (term81 P) = (term81 P).
Proof. exact (eq_refl (term81 P)). Qed.
Lemma lem8215925 {P : Type'} (k : nat) (x : P) : (term82 P x) = (term83 P k x).
Proof. exact (MK_COMB (@lem8215924 P) (@lem8215906 P k x)). Qed.
Lemma lem8215926 {P : Type'} (k : nat) (x : P) : (term83 P k x) = (term76 P k x).
Proof. exact (eq_refl (term83 P k x)). Qed.
Lemma lem8215927 {P : Type'} (x : P) : (term84 P x) = (term84 P x).
Proof. exact (eq_refl (term84 P x)). Qed.
Lemma lem8215928 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = ((term82 P x) = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215927 P x) (@lem8215926 P k x)). Qed.
Lemma lem8215929 {P : Type'} (x : P) : (term82 P x) = x.
Proof. exact (eq_refl (term82 P x)). Qed.
Lemma lem8215930 {P : Type'} : (@eq P) = (@eq P).
Proof. exact (eq_refl (@eq P)). Qed.
Lemma lem8215931 {P : Type'} (x : P) : (term84 P x) = (@eq P x).
Proof. exact (MK_COMB (@lem8215930 P) (@lem8215929 P x)). Qed.
Lemma lem8215932 {P : Type'} (k : nat) (x : P) : (term76 P k x) = (term76 P k x).
Proof. exact (eq_refl (term76 P k x)). Qed.
Lemma lem8215933 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term76 P k x)) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215931 P x) (@lem8215932 P k x)). Qed.
Lemma lem8215934 {P : Type'} (k : nat) (x : P) : ((term82 P x) = (term83 P k x)) = (x = (term76 P k x)).
Proof. exact (TRANS (@lem8215928 P k x) (@lem8215933 P k x)). Qed.
Lemma lem8215935 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215934 P k x) (@lem8215925 P k x)). Qed.
Lemma lem8215936 {P : Type'} (x : P) : (@eq P x) = (@eq P x).
Proof. exact (eq_refl (@eq P x)). Qed.
Lemma lem8215937 {P : Type'} (k : nat) (x : P) : (x = x) = (x = (term76 P k x)).
Proof. exact (MK_COMB (@lem8215936 P x) (@lem8215935 P k x)). Qed.
Lemma lem8215938 {P : Type'} (k : nat) (x : P) : x = (term76 P k x).
Proof. exact (EQ_MP (@lem8215937 P k x) (@lem8215923 P x)). Qed.
Lemma lem8215939 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term190 B C P h g) = (term190 B C P h g).
Proof. exact (eq_refl (term190 B C P h g)). Qed.
Lemma lem8215940 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term191 B C P h g k) = (term192 B C P h g k x).
Proof. exact (MK_COMB (@lem8215939 B C P h g) (@lem8215922 P k x)). Qed.
Lemma lem8215941 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term192 B C P h g k x) = (term193 B C P h g k x).
Proof. exact (eq_refl (term192 B C P h g k x)). Qed.
Lemma lem8215942 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) : (term194 B C P h g k) = (term194 B C P h g k).
Proof. exact (eq_refl (term194 B C P h g k)). Qed.
Lemma lem8215943 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : ((term191 B C P h g k) = (term192 B C P h g k x)) = ((term191 B C P h g k) = (term193 B C P h g k x)).
Proof. exact (MK_COMB (@lem8215942 B C P h g k) (@lem8215941 B C P h g k x)). Qed.
Lemma lem8215944 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) : (term191 B C P h g k) = (term195 B C P h g k).
Proof. exact (eq_refl (term191 B C P h g k)). Qed.
Lemma lem8215945 {P : Type'} : (@eq (P -> nat)) = (@eq (P -> nat)).
Proof. exact (eq_refl (@eq (P -> nat))). Qed.
Lemma lem8215946 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) : (term194 B C P h g k) = (term196 B C P h g k).
Proof. exact (MK_COMB (@lem8215945 P) (@lem8215944 B C P h g k)). Qed.
Lemma lem8215947 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term193 B C P h g k x) = (term193 B C P h g k x).
Proof. exact (eq_refl (term193 B C P h g k x)). Qed.
Lemma lem8215948 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : ((term191 B C P h g k) = (term193 B C P h g k x)) = ((term195 B C P h g k) = (term193 B C P h g k x)).
Proof. exact (MK_COMB (@lem8215946 B C P h g k) (@lem8215947 B C P h g k x)). Qed.
Lemma lem8215949 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : ((term191 B C P h g k) = (term192 B C P h g k x)) = ((term195 B C P h g k) = (term193 B C P h g k x)).
Proof. exact (TRANS (@lem8215943 B C P h g k x) (@lem8215948 B C P h g k x)). Qed.
Lemma lem8215950 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term195 B C P h g k) = (term193 B C P h g k x).
Proof. exact (EQ_MP (@lem8215949 B C P h g k x) (@lem8215940 B C P h g k x)). Qed.
Lemma lem8215951 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term197 B C P h g k x) = (term198 B C P h g k x).
Proof. exact (MK_COMB (@lem8215950 B C P h g k x) (@lem8215938 P k x)). Qed.
Lemma lem8215952 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term198 B C P h g k x) = (term199 B C P h g k x).
Proof. exact (eq_refl (term198 B C P h g k x)). Qed.
Lemma lem8215953 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term200 B C P h g k x) = (term200 B C P h g k x).
Proof. exact (eq_refl (term200 B C P h g k x)). Qed.
Lemma lem8215954 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : ((term197 B C P h g k x) = (term198 B C P h g k x)) = ((term197 B C P h g k x) = (term199 B C P h g k x)).
Proof. exact (MK_COMB (@lem8215953 B C P h g k x) (@lem8215952 B C P h g k x)). Qed.
Lemma lem8215955 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term197 B C P h g k x) = (h g x k).
Proof. exact (eq_refl (term197 B C P h g k x)). Qed.
Lemma lem8215956 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8215957 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term200 B C P h g k x) = (term201 B C P h g x k).
Proof. exact (MK_COMB (@lem8215956) (@lem8215955 B C P h g x k)). Qed.
Lemma lem8215958 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term199 B C P h g k x) = (term199 B C P h g k x).
Proof. exact (eq_refl (term199 B C P h g k x)). Qed.
Lemma lem8215959 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : ((term197 B C P h g k x) = (term199 B C P h g k x)) = ((h g x k) = (term199 B C P h g k x)).
Proof. exact (MK_COMB (@lem8215957 B C P h g x k) (@lem8215958 B C P h g k x)). Qed.
Lemma lem8215960 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : ((term197 B C P h g k x) = (term198 B C P h g k x)) = ((h g x k) = (term199 B C P h g k x)).
Proof. exact (TRANS (@lem8215954 B C P h g k x) (@lem8215959 B C P h g k x)). Qed.
Lemma lem8215961 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (h g x k) = (term199 B C P h g k x).
Proof. exact (EQ_MP (@lem8215960 B C P h g k x) (@lem8215951 B C P h g k x)). Qed.
Lemma lem8215962 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term199 B C P h g k x) = (h g x k).
Proof. exact (SYM (@lem8215961 B C P h g k x)). Qed.
Lemma lem8215963 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : (term202 B C P h g k x) = (term199 B C P h g k x).
Proof. exact (eq_refl (term202 B C P h g k x)). Qed.
Lemma lem8215964 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term202 B C P h g k x) = (h g x k).
Proof. exact (TRANS (@lem8215963 B C P h g k x) (@lem8215962 B C P h g x k)). Qed.
Lemma lem8215965 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) : term203 B C P h g k.
Proof. exact (fun x : P => @lem8215964 B C P h g x k). Qed.
Lemma lem8215966 {B C P : Type'} (h : type555 B C P) (g : B -> C) : term204 B C P h g.
Proof. exact (fun k : nat => @lem8215965 B C P h g k). Qed.
Lemma lem8215967 {B C P : Type'} (h : type555 B C P) (g : B -> C) : term205 B C P h g.
Proof. exact (ex_intro (term206 B C P h g) (term207 B C P h g) (@lem8215966 B C P h g)). Qed.
Lemma lem8215969 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem8215970 (a : nat) (b : nat) : (a = b) = (@GEQ nat a b).
Proof. exact (@lem8215969 nat a b). Qed.
Lemma lem8215971 {B C P : Type'} (_109195 : type1311 P) (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : ((term208 P _109195 k x) = (h g x k)) = (term209 B C P _109195 h g x k).
Proof. exact (@lem8215970 (term208 P _109195 k x) (h g x k)). Qed.
Lemma lem8215972 {B C P : Type'} (_109195 : type1311 P) (h : type555 B C P) (g : B -> C) (k : nat) : (term210 B C P _109195 h g k) = (term211 B C P _109195 h g k).
Proof. exact (fun_ext (fun x : P => @lem8215971 B C P _109195 h g x k)). Qed.
Lemma lem8215973 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8215974 {B C P : Type'} (_109195 : type1311 P) (h : type555 B C P) (g : B -> C) (k : nat) : (term212 B C P _109195 h g k) = (term213 B C P _109195 h g k).
Proof. exact (MK_COMB (@lem8215973 P) (@lem8215972 B C P _109195 h g k)). Qed.
Lemma lem8215975 {B C P : Type'} (_109195 : type1311 P) (h : type555 B C P) (g : B -> C) : (term214 B C P _109195 h g) = (term215 B C P _109195 h g).
Proof. exact (fun_ext (fun k : nat => @lem8215974 B C P _109195 h g k)). Qed.
Lemma lem8215976 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8215977 {B C P : Type'} (_109195 : type1311 P) (h : type555 B C P) (g : B -> C) : (term216 B C P _109195 h g) = (term217 B C P _109195 h g).
Proof. exact (MK_COMB (@lem8215976) (@lem8215975 B C P _109195 h g)). Qed.
Lemma lem8215978 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term206 B C P h g) = (term218 B C P h g).
Proof. exact (fun_ext (fun _109195 : type1311 P => @lem8215977 B C P _109195 h g)). Qed.
Lemma lem8215979 {P : Type'} : (@ex ((prod nat P) -> nat)) = (@ex ((prod nat P) -> nat)).
Proof. exact (eq_refl (@ex ((prod nat P) -> nat))). Qed.
Lemma lem8215980 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term205 B C P h g) = (term219 B C P h g).
Proof. exact (MK_COMB (@lem8215979 P) (@lem8215978 B C P h g)). Qed.
Lemma lem8215981 {B C P : Type'} (h : type555 B C P) (g : B -> C) : term219 B C P h g.
Proof. exact (EQ_MP (@lem8215980 B C P h g) (@lem8215967 B C P h g)). Qed.
Lemma lem8215983 {_5076 : Type'} (P : _5076 -> Prop) : term116 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem8215984 {P : Type'} (P' : type373 P) : term220 P P'.
Proof. exact (@lem8215983 (type1311 P) P'). Qed.
Lemma lem8215985 {B C P : Type'} (h : type555 B C P) (g : B -> C) : term221 B C P h g.
Proof. exact (@lem8215984 P (term218 B C P h g)). Qed.
Lemma lem8215986 {B C P : Type'} (h : type555 B C P) (g : B -> C) : term222 B C P h g.
Proof. exact (@lem8215985 B C P h g (@lem8215981 B C P h g)). Qed.
Lemma lem8215987 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (term222 B C P h g) = (term223 B C P h g).
Proof. exact (eq_refl (term222 B C P h g)). Qed.
Lemma lem8215988 {B C P : Type'} (h : type555 B C P) (g : B -> C) : term223 B C P h g.
Proof. exact (EQ_MP (@lem8215987 B C P h g) (@lem8215986 B C P h g)). Qed.
Lemma lem8215989 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) : term224 B C P h g k.
Proof. exact (@lem8215988 B C P h g k). Qed.
Lemma lem8215990 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) : (term224 B C P h g k) = (term225 B C P h g k).
Proof. exact (eq_refl (term224 B C P h g k)). Qed.
Lemma lem8215991 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) : term225 B C P h g k.
Proof. exact (EQ_MP (@lem8215990 B C P h g k) (@lem8215989 B C P h g k)). Qed.
Lemma lem8215992 {B C P : Type'} (h : type555 B C P) (g : B -> C) (k : nat) (x : P) : term226 B C P h g k x.
Proof. exact (@lem8215991 B C P h g k x). Qed.
Lemma lem8215993 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term226 B C P h g k x) = (term227 B C P h g x k).
Proof. exact (eq_refl (term226 B C P h g k x)). Qed.
Lemma lem8215994 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : term227 B C P h g x k.
Proof. exact (EQ_MP (@lem8215993 B C P h g x k) (@lem8215992 B C P h g k x)). Qed.
Lemma lem8215996 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem8215997 (a : nat) (b : nat) : (@GEQ nat a b) = (a = b).
Proof. exact (@lem8215996 nat a b). Qed.
Lemma lem8215998 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term227 B C P h g x k) = ((term189 B C P h g k x) = (h g x k)).
Proof. exact (@lem8215997 (term189 B C P h g k x) (h g x k)). Qed.
Lemma lem8215999 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term189 B C P h g k x) = (h g x k).
Proof. exact (EQ_MP (@lem8215998 B C P h g x k) (@lem8215994 B C P h g x k)). Qed.
Lemma lem8216000 {B C P : Type'} (h : type555 B C P) (g : B -> C) (x : P) (k : nat) : (term189 B C P h g k x) = (h g x k).
Proof. exact (@lem8215999 B C P h g x k). Qed.
Lemma lem8216001 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term189 B C P h g p1 p2) = (h g p2 p1).
Proof. exact (@lem8216000 B C P h g p2 p1). Qed.
Lemma lem8216002 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term188 B C P h g p1 p2) = (h g p2 p1).
Proof. exact (TRANS (@lem8215902 B C P h g p1 p2) (@lem8216001 B C P h g p2 p1)). Qed.
Lemma lem8216003 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((term188 B C P h f p1 p2) = (term188 B C P h g p1 p2)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (MK_COMB (@lem8215875 B C P h f p2 p1) (@lem8216002 B C P h g p2 p1)). Qed.
Lemma lem8216006 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term57 A B C P a b p lt2 s f h g p1 p2) = (term229 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8215744 A B C P a p1 b p lt2 s p2 f g) (@lem8216003 B C P f h g p2 p1)). Qed.
Lemma lem8216009 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term59 A B C P a b p lt2 s f h g p1) = (term230 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8216006 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216010 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216011 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term61 A B C P a b p lt2 s f h g p1) = (term231 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8216010 P) (@lem8216009 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216018 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term63 A B C P a b p lt2 s f h g) = (term232 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8216011 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8216020 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term64 A B C P a b p lt2 s f h g) = (term233 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8216019) (@lem8216018 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216027 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term53 A B C P a b p lt2 s f h g) = (term233 A B C P a b p lt2 s f h g).
Proof. exact (TRANS (@lem8215318 A B C P a b p lt2 s f h g) (@lem8216020 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216028 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term234 A B C P a b p lt2 s f h) = (term235 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8216027 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216029 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216030 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term236 A B C P a b p lt2 s f h) = (term237 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8216029 B C) (@lem8216028 A B C P a b p lt2 s f h)). Qed.
Lemma lem8216037 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term238 A B C P a b p lt2 s h) = (term239 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8216030 A B C P a b p lt2 s f h)). Qed.
Lemma lem8216038 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216039 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term41 A B C P a b p lt2 s h) = (term240 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8216038 B C) (@lem8216037 A B C P a b p lt2 s h)). Qed.
Lemma lem8216046 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term40 A B C P lt2 a b p s h) = (term240 A B C P a b p lt2 s h).
Proof. exact (TRANS (@lem8215283 A B C P a b p lt2 s h) (@lem8216039 A B C P a b p lt2 s h)). Qed.
Lemma lem8216047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8216048 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term241 A B C P lt2 a b p s h) = (term242 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8216047) (@lem8216046 A B C P a b p lt2 s h)). Qed.
Lemma lem8216050 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term38 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8215240 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8215239 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8216051 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (t : type561 B C P) : (@admissible A C B nat P lt2 p s t) = (term243 A B C P p lt2 s t).
Proof. exact (@lem8216050 A C B nat P p lt2 s t). Qed.
Lemma lem8216052 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term244 A B C P lt2 p s a b h) = (term245 A B C P p lt2 s a b h).
Proof. exact (@lem8216051 A B C P p lt2 s (term246 B C P a b h)). Qed.
Lemma lem8216090 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8216091 {B C P : Type'} (f : type561 B C P) (y : B -> C) : (term247 B C P f y) = (f y).
Proof. exact (@lem8216090 (B -> C) (P -> nat) f y). Qed.
Lemma lem8216092 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term248 B C P a b h f) = (term249 B C P a b h f).
Proof. exact (@lem8216091 B C P (term246 B C P a b h) f). Qed.
Lemma lem8216093 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (eq_refl (term249 B C P a b h f)). Qed.
Lemma lem8216094 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term251 B C P a b h) = (term246 B C P a b h).
Proof. exact (fun_ext (fun f : B -> C => @lem8216093 B C P a b h f)). Qed.
Lemma lem8216095 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8216096 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term248 B C P a b h f) = (term249 B C P a b h f).
Proof. exact (MK_COMB (@lem8216094 B C P a b h) (@lem8216095 B C f)). Qed.
Lemma lem8216097 {P : Type'} : (@eq (P -> nat)) = (@eq (P -> nat)).
Proof. exact (eq_refl (@eq (P -> nat))). Qed.
Lemma lem8216098 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term252 B C P a b h f) = (term253 B C P a b h f).
Proof. exact (MK_COMB (@lem8216097 P) (@lem8216096 B C P a b h f)). Qed.
Lemma lem8216099 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (eq_refl (term249 B C P a b h f)). Qed.
Lemma lem8216100 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : ((term248 B C P a b h f) = (term249 B C P a b h f)) = ((term249 B C P a b h f) = (term250 B C P a b h f)).
Proof. exact (MK_COMB (@lem8216098 B C P a b h f) (@lem8216099 B C P a b h f)). Qed.
Lemma lem8216101 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (EQ_MP (@lem8216100 B C P a b h f) (@lem8216092 B C P a b h f)). Qed.
Lemma lem8216102 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8216103 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term254 B C P a b h f a') = (term255 B C P a b h f a').
Proof. exact (MK_COMB (@lem8216101 B C P a b h f) (@lem8216102 P a')). Qed.
Lemma lem8216105 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8216106 {P : Type'} (f : P -> nat) (y : P) : (term256 P f y) = (f y).
Proof. exact (@lem8216105 P nat f y). Qed.
Lemma lem8216107 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term257 B C P a b h f a') = (term255 B C P a b h f a').
Proof. exact (@lem8216106 P (term250 B C P a b h f) a'). Qed.
Lemma lem8216108 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (x : P) : (term255 B C P a b h f x) = (term258 B C P a b h f x).
Proof. exact (eq_refl (term255 B C P a b h f x)). Qed.
Lemma lem8216109 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term259 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (fun_ext (fun x : P => @lem8216108 B C P a b h f x)). Qed.
Lemma lem8216110 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8216111 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term257 B C P a b h f a') = (term255 B C P a b h f a').
Proof. exact (MK_COMB (@lem8216109 B C P a b h f) (@lem8216110 P a')). Qed.
Lemma lem8216112 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8216113 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term260 B C P a b h f a') = (term261 B C P a b h f a').
Proof. exact (MK_COMB (@lem8216112) (@lem8216111 B C P a b h f a')). Qed.
Lemma lem8216114 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term255 B C P a b h f a') = (term258 B C P a b h f a').
Proof. exact (eq_refl (term255 B C P a b h f a')). Qed.
Lemma lem8216115 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : ((term257 B C P a b h f a') = (term255 B C P a b h f a')) = ((term255 B C P a b h f a') = (term258 B C P a b h f a')).
Proof. exact (MK_COMB (@lem8216113 B C P a b h f a') (@lem8216114 B C P a b h f a')). Qed.
Lemma lem8216116 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term255 B C P a b h f a') = (term258 B C P a b h f a').
Proof. exact (EQ_MP (@lem8216115 B C P a b h f a') (@lem8216107 B C P a b h f a')). Qed.
Lemma lem8216117 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term254 B C P a b h f a') = (term258 B C P a b h f a').
Proof. exact (TRANS (@lem8216103 B C P a b h f a') (@lem8216116 B C P a b h f a')). Qed.
Lemma lem8216118 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8216119 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (a' : P) : (term262 B C P a b h f a') = (term263 B C P a b h f a').
Proof. exact (MK_COMB (@lem8216118) (@lem8216117 B C P a b h f a')). Qed.
Lemma lem8216121 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8216122 {B C P : Type'} (f : type561 B C P) (y : B -> C) : (term247 B C P f y) = (f y).
Proof. exact (@lem8216121 (B -> C) (P -> nat) f y). Qed.
Lemma lem8216123 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term248 B C P a b h g) = (term249 B C P a b h g).
Proof. exact (@lem8216122 B C P (term246 B C P a b h) g). Qed.
Lemma lem8216124 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) : (term249 B C P a b h f) = (term250 B C P a b h f).
Proof. exact (eq_refl (term249 B C P a b h f)). Qed.
Lemma lem8216125 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term251 B C P a b h) = (term246 B C P a b h).
Proof. exact (fun_ext (fun f : B -> C => @lem8216124 B C P a b h f)). Qed.
Lemma lem8216126 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8216127 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term248 B C P a b h g) = (term249 B C P a b h g).
Proof. exact (MK_COMB (@lem8216125 B C P a b h) (@lem8216126 B C g)). Qed.
Lemma lem8216128 {P : Type'} : (@eq (P -> nat)) = (@eq (P -> nat)).
Proof. exact (eq_refl (@eq (P -> nat))). Qed.
Lemma lem8216129 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term252 B C P a b h g) = (term253 B C P a b h g).
Proof. exact (MK_COMB (@lem8216128 P) (@lem8216127 B C P a b h g)). Qed.
Lemma lem8216130 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term249 B C P a b h g) = (term250 B C P a b h g).
Proof. exact (eq_refl (term249 B C P a b h g)). Qed.
Lemma lem8216131 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : ((term248 B C P a b h g) = (term249 B C P a b h g)) = ((term249 B C P a b h g) = (term250 B C P a b h g)).
Proof. exact (MK_COMB (@lem8216129 B C P a b h g) (@lem8216130 B C P a b h g)). Qed.
Lemma lem8216132 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term249 B C P a b h g) = (term250 B C P a b h g).
Proof. exact (EQ_MP (@lem8216131 B C P a b h g) (@lem8216123 B C P a b h g)). Qed.
Lemma lem8216133 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8216134 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term254 B C P a b h g a') = (term255 B C P a b h g a').
Proof. exact (MK_COMB (@lem8216132 B C P a b h g) (@lem8216133 P a')). Qed.
Lemma lem8216136 {A B : Type'} (f : A -> B) (y : A) : (term65 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8216137 {P : Type'} (f : P -> nat) (y : P) : (term256 P f y) = (f y).
Proof. exact (@lem8216136 P nat f y). Qed.
Lemma lem8216138 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term257 B C P a b h g a') = (term255 B C P a b h g a').
Proof. exact (@lem8216137 P (term250 B C P a b h g) a'). Qed.
Lemma lem8216139 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (x : P) : (term255 B C P a b h g x) = (term258 B C P a b h g x).
Proof. exact (eq_refl (term255 B C P a b h g x)). Qed.
Lemma lem8216140 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term259 B C P a b h g) = (term250 B C P a b h g).
Proof. exact (fun_ext (fun x : P => @lem8216139 B C P a b h g x)). Qed.
Lemma lem8216141 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8216142 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term257 B C P a b h g a') = (term255 B C P a b h g a').
Proof. exact (MK_COMB (@lem8216140 B C P a b h g) (@lem8216141 P a')). Qed.
Lemma lem8216143 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8216144 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term260 B C P a b h g a') = (term261 B C P a b h g a').
Proof. exact (MK_COMB (@lem8216143) (@lem8216142 B C P a b h g a')). Qed.
Lemma lem8216145 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term255 B C P a b h g a') = (term258 B C P a b h g a').
Proof. exact (eq_refl (term255 B C P a b h g a')). Qed.
Lemma lem8216146 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : ((term257 B C P a b h g a') = (term255 B C P a b h g a')) = ((term255 B C P a b h g a') = (term258 B C P a b h g a')).
Proof. exact (MK_COMB (@lem8216144 B C P a b h g a') (@lem8216145 B C P a b h g a')). Qed.
Lemma lem8216147 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term255 B C P a b h g a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8216146 B C P a b h g a') (@lem8216138 B C P a b h g a')). Qed.
Lemma lem8216148 {B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term254 B C P a b h g a') = (term258 B C P a b h g a').
Proof. exact (TRANS (@lem8216134 B C P a b h g a') (@lem8216147 B C P a b h g a')). Qed.
Lemma lem8216149 {B C P : Type'} (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : ((term254 B C P a b h f a') = (term254 B C P a b h g a')) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (MK_COMB (@lem8216119 B C P a b h f a') (@lem8216148 B C P a b h g a')). Qed.
Lemma lem8216152 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P) (f : B -> C) (g : B -> C) : (term264 A B C P p lt2 s a f g) = (term264 A B C P p lt2 s a f g).
Proof. exact (eq_refl (term264 A B C P p lt2 s a f g)). Qed.
Lemma lem8216153 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : (term265 A B C P p lt2 s f a b h g a') = (term266 A B C P p lt2 s f a b h g a').
Proof. exact (MK_COMB (@lem8216152 A B C P p lt2 s a' f g) (@lem8216149 B C P f a b h g a')). Qed.
Lemma lem8216156 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term267 A B C P p lt2 s f a b h g) = (term268 A B C P p lt2 s f a b h g).
Proof. exact (fun_ext (fun a' : P => @lem8216153 A B C P p lt2 s f a b h g a')). Qed.
Lemma lem8216157 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216158 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) : (term269 A B C P p lt2 s f a b h g) = (term270 A B C P p lt2 s f a b h g).
Proof. exact (MK_COMB (@lem8216157 P) (@lem8216156 A B C P p lt2 s f a b h g)). Qed.
Lemma lem8216165 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term271 A B C P p lt2 s f a b h) = (term272 A B C P p lt2 s f a b h).
Proof. exact (fun_ext (fun g : B -> C => @lem8216158 A B C P p lt2 s f a b h g)). Qed.
Lemma lem8216166 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216167 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term273 A B C P p lt2 s f a b h) = (term274 A B C P p lt2 s f a b h).
Proof. exact (MK_COMB (@lem8216166 B C) (@lem8216165 A B C P p lt2 s f a b h)). Qed.
Lemma lem8216174 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term275 A B C P p lt2 s a b h) = (term276 A B C P p lt2 s a b h).
Proof. exact (fun_ext (fun f : B -> C => @lem8216167 A B C P p lt2 s f a b h)). Qed.
Lemma lem8216175 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216176 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term245 A B C P p lt2 s a b h) = (term277 A B C P p lt2 s a b h).
Proof. exact (MK_COMB (@lem8216175 B C) (@lem8216174 A B C P p lt2 s a b h)). Qed.
Lemma lem8216183 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term244 A B C P lt2 p s a b h) = (term277 A B C P p lt2 s a b h).
Proof. exact (TRANS (@lem8216052 A B C P p lt2 s a b h) (@lem8216176 A B C P p lt2 s a b h)). Qed.
Lemma lem8216184 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : (term278 A B C P lt2 p s a b h) = (term279 A B C P p lt2 s a b h).
Proof. exact (MK_COMB (@lem8216048 A B C P a b p lt2 s h) (@lem8216183 A B C P p lt2 s a b h)). Qed.
Lemma lem8216187 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (h : type555 B C P) : (term280 A B C P lt2 p s a h) = (term281 A B C P p lt2 s a h).
Proof. exact (fun_ext (fun b : P -> nat => @lem8216184 A B C P p lt2 s a b h)). Qed.
Lemma lem8216188 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8216189 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (h : type555 B C P) : (term282 A B C P lt2 p s a h) = (term283 A B C P p lt2 s a h).
Proof. exact (MK_COMB (@lem8216188 P) (@lem8216187 A B C P p lt2 s a h)). Qed.
Lemma lem8216196 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term284 A B C P lt2 p s h) = (term285 A B C P p lt2 s h).
Proof. exact (fun_ext (fun a : P -> nat => @lem8216189 A B C P p lt2 s a h)). Qed.
Lemma lem8216197 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8216198 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term286 A B C P lt2 p s h) = (term287 A B C P p lt2 s h).
Proof. exact (MK_COMB (@lem8216197 P) (@lem8216196 A B C P p lt2 s h)). Qed.
Lemma lem8216205 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) : (term288 A B C P lt2 p s) = (term289 A B C P p lt2 s).
Proof. exact (fun_ext (fun h : type555 B C P => @lem8216198 A B C P p lt2 s h)). Qed.
Lemma lem8216206 {B C P : Type'} : (@all ((B -> C) -> P -> nat -> nat)) = (@all ((B -> C) -> P -> nat -> nat)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> nat -> nat))). Qed.
Lemma lem8216207 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) : (term290 A B C P lt2 p s) = (term291 A B C P p lt2 s).
Proof. exact (MK_COMB (@lem8216206 B C P) (@lem8216205 A B C P p lt2 s)). Qed.
Lemma lem8216214 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) : (term292 A B C P lt2 p) = (term293 A B C P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8216207 A B C P p lt2 s)). Qed.
Lemma lem8216215 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8216216 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) : (term294 A B C P lt2 p) = (term295 A B C P p lt2).
Proof. exact (MK_COMB (@lem8216215 A P) (@lem8216214 A B C P p lt2)). Qed.
Lemma lem8216223 {A B C P : Type'} (lt2 : type1470 A B) : (term296 A B C P lt2) = (term297 A B C P lt2).
Proof. exact (fun_ext (fun p : type560 B C P => @lem8216216 A B C P p lt2)). Qed.
Lemma lem8216224 {B C P : Type'} : (@all ((B -> C) -> P -> Prop)) = (@all ((B -> C) -> P -> Prop)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> Prop))). Qed.
Lemma lem8216225 {A B C P : Type'} (lt2 : type1470 A B) : (term298 A B C P lt2) = (term299 A B C P lt2).
Proof. exact (MK_COMB (@lem8216224 B C P) (@lem8216223 A B C P lt2)). Qed.
Lemma lem8216232 {A B C P : Type'} : (term300 A B C P) = (term301 A B C P).
Proof. exact (fun_ext (fun lt2 : type1470 A B => @lem8216225 A B C P lt2)). Qed.
Lemma lem8216233 {A B : Type'} : (@all (B -> A -> Prop)) = (@all (B -> A -> Prop)).
Proof. exact (eq_refl (@all (B -> A -> Prop))). Qed.
Lemma lem8216234 {A B C P : Type'} : (term302 A B C P) = (term303 A B C P).
Proof. exact (MK_COMB (@lem8216233 A B) (@lem8216232 A B C P)). Qed.
Lemma lem8216241 {A B C P : Type'} : (term303 A B C P) = (term302 A B C P).
Proof. exact (SYM (@lem8216234 A B C P)). Qed.
Lemma lem8216242 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term240 A B C P a b p lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8216243 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term304 A B C P p lt2 s a' f g) : term304 A B C P p lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8216244 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term305 A B C P p lt2 s a' f g) : term305 A B C P p lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8216245 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : p f a'.
Proof. exact (h1). Qed.
Lemma lem8216246 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term174 A B C P lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8216247 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : p g a'.
Proof. exact (h1). Qed.
Lemma lem8216249 (f : nat -> nat) (m : nat) (n : nat) (g : nat -> nat) : term15 f m n g.
Proof. exact (EQ_MP (@lem8215225 f m n g) (@lem8215224 f m n g)). Qed.
Lemma lem8216250 {B C P : Type'} (f : B -> C) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (g : B -> C) (a' : P) : term306 B C P f a b h g a'.
Proof. exact (@lem8216249 (h f a') (a a') (b a') (h g a')). Qed.
Lemma lem8216252 (p : Prop) : p = (term307 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8216253 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term308 B C P a b f h g a') = (term309 B C P a b f h g a').
Proof. exact (@lem8216252 (term308 B C P a b f h g a')). Qed.
Lemma lem8216254 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term309 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (SYM (@lem8216253 B C P a b f h g a')). Qed.
Lemma lem8216255 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term310 B C P a b f h g a') : term310 B C P a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8216258 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8216259 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term311 A B C P p lt2 s a b f h g a' => @lem8216258 A B C P p lt2 s a b f h g a' h0). Qed.
Lemma lem8216260 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term312 A B C P p lt2 s a b f h g a') : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8216261 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8216262 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') (h2 : term312 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8216260 A B C P p lt2 s a b f h g a' h2 (@lem8216261 A B C P p lt2 s a b f h g a' h1)). Qed.
Lemma lem8216263 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') : term313 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term312 A B C P p lt2 s a b f h g a' => @lem8216262 A B C P p lt2 s a b f h g a' h1 h0). Qed.
Lemma lem8216264 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term312 A B C P p lt2 s a b f h g a') : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (h1). Qed.
Lemma lem8216265 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term311 A B C P p lt2 s a b f h g a') (h2 : term312 A B C P p lt2 s a b f h g a') : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8216263 A B C P p lt2 s a b f h g a' h1 (@lem8216264 A B C P p lt2 s a b f h g a' h2)). Qed.
Lemma lem8216266 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (h1 : term312 A B C P p lt2 s a b f h g a') : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term311 A B C P p lt2 s a b f h g a' => @lem8216265 A B C P p lt2 s a b f h g a' h0 h1). Qed.
Lemma lem8216267 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term314 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term312 A B C P p lt2 s a b f h g a' => @lem8216266 A B C P p lt2 s a b f h g a' h0). Qed.
Lemma lem8216270 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8216267 A B C P p lt2 s a b f h g a' (@lem8216259 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8216271 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term312 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8216270 A B C P p lt2 s a b f h g a'). Qed.
Lemma lem8216359 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8216360 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term309 B C P a b f h g a') = (term315 B C P a b f h g a').
Proof. exact (@lem8216359 (term310 B C P a b f h g a')). Qed.
Lemma lem8216362 (t : Prop) : (term316 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8216363 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term315 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (@lem8216362 (term308 B C P a b f h g a')). Qed.
Lemma lem8216368 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term309 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (TRANS (@lem8216360 B C P a b f h g a') (@lem8216363 B C P a b f h g a')). Qed.
Lemma lem8216373 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term317 A B C P lt2 s a' f g) = (term317 A B C P lt2 s a' f g).
Proof. exact (eq_refl (term317 A B C P lt2 s a' f g)). Qed.
Lemma lem8216374 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term318 A B C P lt2 s a b f h g a') = (term319 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216373 A B C P lt2 s a' f g) (@lem8216368 B C P a b f h g a')). Qed.
Lemma lem8216377 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term320 B C P p g a') = (term320 B C P p g a').
Proof. exact (eq_refl (term320 B C P p g a')). Qed.
Lemma lem8216378 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term321 A B C P p lt2 s a b f h g a') = (term322 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216377 B C P p g a') (@lem8216374 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8216381 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term320 B C P p f a') = (term320 B C P p f a').
Proof. exact (eq_refl (term320 B C P p f a')). Qed.
Lemma lem8216382 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term323 A B C P p lt2 s a b f h g a') = (term324 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216381 B C P p f a') (@lem8216378 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8216385 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term242 A B C P a b p lt2 s h) = (term242 A B C P a b p lt2 s h).
Proof. exact (eq_refl (term242 A B C P a b p lt2 s h)). Qed.
Lemma lem8216386 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term311 A B C P p lt2 s a b f h g a') = (term325 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216385 A B C P a b p lt2 s h) (@lem8216382 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8216389 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term326 A B C P lt2 s a b f h g a') = (term327 A B C P lt2 s a b f h g a').
Proof. exact (fun_ext (fun p : type560 B C P => @lem8216386 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8216390 {B C P : Type'} : (@all ((B -> C) -> P -> Prop)) = (@all ((B -> C) -> P -> Prop)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> Prop))). Qed.
Lemma lem8216391 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term328 A B C P lt2 s a b f h g a') = (term329 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216390 B C P) (@lem8216389 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8216396 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term330 A B C P s a b f h g a') = (term331 A B C P s a b f h g a').
Proof. exact (fun_ext (fun lt2 : type1470 A B => @lem8216391 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8216397 {A B : Type'} : (@all (B -> A -> Prop)) = (@all (B -> A -> Prop)).
Proof. exact (eq_refl (@all (B -> A -> Prop))). Qed.
Lemma lem8216398 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term332 A B C P s a b f h g a') = (term333 A B C P s a b f h g a').
Proof. exact (MK_COMB (@lem8216397 A B) (@lem8216396 A B C P s a b f h g a')). Qed.
Lemma lem8216403 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term334 A B C P a b f h g a') = (term335 A B C P a b f h g a').
Proof. exact (fun_ext (fun s : P -> A => @lem8216398 A B C P s a b f h g a')). Qed.
Lemma lem8216404 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8216405 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term336 A B C P a b f h g a') = (term337 A B C P a b f h g a').
Proof. exact (MK_COMB (@lem8216404 A P) (@lem8216403 A B C P a b f h g a')). Qed.
Lemma lem8216410 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term338 A B C P b f h g a') = (term339 A B C P b f h g a').
Proof. exact (fun_ext (fun a : P -> nat => @lem8216405 A B C P a b f h g a')). Qed.
Lemma lem8216411 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8216412 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term340 A B C P b f h g a') = (term341 A B C P b f h g a').
Proof. exact (MK_COMB (@lem8216411 P) (@lem8216410 A B C P b f h g a')). Qed.
Lemma lem8216417 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term342 A B C P f h g a') = (term343 A B C P f h g a').
Proof. exact (fun_ext (fun b : P -> nat => @lem8216412 A B C P b f h g a')). Qed.
Lemma lem8216418 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8216419 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term344 A B C P f h g a') = (term345 A B C P f h g a').
Proof. exact (MK_COMB (@lem8216418 P) (@lem8216417 A B C P f h g a')). Qed.
Lemma lem8216424 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (term346 A B C P h g a') = (term347 A B C P h g a').
Proof. exact (fun_ext (fun f : B -> C => @lem8216419 A B C P f h g a')). Qed.
Lemma lem8216425 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216426 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (term348 A B C P h g a') = (term349 A B C P h g a').
Proof. exact (MK_COMB (@lem8216425 B C) (@lem8216424 A B C P h g a')). Qed.
Lemma lem8216431 {A B C P : Type'} (g : B -> C) (a' : P) : (term350 A B C P g a') = (term351 A B C P g a').
Proof. exact (fun_ext (fun h : type555 B C P => @lem8216426 A B C P h g a')). Qed.
Lemma lem8216432 {B C P : Type'} : (@all ((B -> C) -> P -> nat -> nat)) = (@all ((B -> C) -> P -> nat -> nat)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> nat -> nat))). Qed.
Lemma lem8216433 {A B C P : Type'} (g : B -> C) (a' : P) : (term352 A B C P g a') = (term353 A B C P g a').
Proof. exact (MK_COMB (@lem8216432 B C P) (@lem8216431 A B C P g a')). Qed.
Lemma lem8216438 {A B C P : Type'} (a' : P) : (term354 A B C P a') = (term355 A B C P a').
Proof. exact (fun_ext (fun g : B -> C => @lem8216433 A B C P g a')). Qed.
Lemma lem8216439 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216440 {A B C P : Type'} (a' : P) : (term356 A B C P a') = (term357 A B C P a').
Proof. exact (MK_COMB (@lem8216439 B C) (@lem8216438 A B C P a')). Qed.
Lemma lem8216445 {A B C P : Type'} : (term358 A B C P) = (term359 A B C P).
Proof. exact (fun_ext (fun a' : P => @lem8216440 A B C P a')). Qed.
Lemma lem8216446 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216455 {A B C P : Type'} : (term360 A B C P) = (term361 A B C P).
Proof. exact (MK_COMB (@lem8216446 P) (@lem8216445 A B C P)). Qed.
Lemma lem8216464 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (term362 B C P a b f h g a' i) = (term362 B C P a b f h g a' i).
Proof. exact (eq_refl (term362 B C P a b f h g a' i)). Qed.
Lemma lem8216465 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term363 B C P a b f h g a') = (term363 B C P a b f h g a').
Proof. exact (fun_ext (fun i : nat => @lem8216464 B C P a b f h g a' i)). Qed.
Lemma lem8216466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8216467 {B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term308 B C P a b f h g a') = (term308 B C P a b f h g a').
Proof. exact (MK_COMB (@lem8216466) (@lem8216465 B C P a b f h g a')). Qed.
Lemma lem8216472 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term170 A B C P lt2 s a' f g z) = (term170 A B C P lt2 s a' f g z).
Proof. exact (eq_refl (term170 A B C P lt2 s a' f g z)). Qed.
Lemma lem8216473 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term172 A B C P lt2 s a' f g) = (term172 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8216472 A B C P lt2 s a' f g z)). Qed.
Lemma lem8216474 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8216475 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term174 A B C P lt2 s a' f g) = (term174 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8216474 B) (@lem8216473 A B C P lt2 s a' f g)). Qed.
Lemma lem8216476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8216477 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term317 A B C P lt2 s a' f g) = (term317 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8216476) (@lem8216475 A B C P lt2 s a' f g)). Qed.
Lemma lem8216478 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term319 A B C P lt2 s a b f h g a') = (term319 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216477 A B C P lt2 s a' f g) (@lem8216467 B C P a b f h g a')). Qed.
Lemma lem8216481 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term320 B C P p g a') = (term320 B C P p g a').
Proof. exact (eq_refl (term320 B C P p g a')). Qed.
Lemma lem8216482 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term322 A B C P p lt2 s a b f h g a') = (term322 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216481 B C P p g a') (@lem8216478 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8216485 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term320 B C P p f a') = (term320 B C P p f a').
Proof. exact (eq_refl (term320 B C P p f a')). Qed.
Lemma lem8216486 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term324 A B C P p lt2 s a b f h g a') = (term324 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216485 B C P p f a') (@lem8216482 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8216487 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8216492 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term170 A B C P lt2 s p2 f g z) = (term170 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term170 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216493 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term172 A B C P lt2 s p2 f g) = (term172 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8216492 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216494 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8216495 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term174 A B C P lt2 s p2 f g) = (term174 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216494 B) (@lem8216493 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216506 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term126 B C P a p1 b p g p2) = (term126 B C P a p1 b p g p2).
Proof. exact (eq_refl (term126 B C P a p1 b p g p2)). Qed.
Lemma lem8216507 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term176 A B C P a p1 b p lt2 s p2 f g) = (term176 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216506 B C P a p1 b p g p2) (@lem8216495 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216518 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term126 B C P a p1 b p f p2) = (term126 B C P a p1 b p f p2).
Proof. exact (eq_refl (term126 B C P a p1 b p f p2)). Qed.
Lemma lem8216519 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term178 A B C P a p1 b p lt2 s p2 f g) = (term178 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216518 B C P a p1 b p f p2) (@lem8216507 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216520 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8216521 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term180 A B C P a p1 b p lt2 s p2 f g) = (term180 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216520) (@lem8216519 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216522 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term229 A B C P a b p lt2 s f h g p2 p1) = (term229 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8216521 A B C P a p1 b p lt2 s p2 f g) (@lem8216487 B C P f h g p2 p1)). Qed.
Lemma lem8216523 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term230 A B C P a b p lt2 s f h g p1) = (term230 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8216522 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216524 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216525 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term231 A B C P a b p lt2 s f h g p1) = (term231 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8216524 P) (@lem8216523 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216526 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term232 A B C P a b p lt2 s f h g) = (term232 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8216525 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216527 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8216528 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term233 A B C P a b p lt2 s f h g) = (term233 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8216527) (@lem8216526 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216529 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term235 A B C P a b p lt2 s f h) = (term235 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8216528 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216530 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216531 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term237 A B C P a b p lt2 s f h) = (term237 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8216530 B C) (@lem8216529 A B C P a b p lt2 s f h)). Qed.
Lemma lem8216532 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term239 A B C P a b p lt2 s h) = (term239 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8216531 A B C P a b p lt2 s f h)). Qed.
Lemma lem8216533 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216534 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term240 A B C P a b p lt2 s h) = (term240 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8216533 B C) (@lem8216532 A B C P a b p lt2 s h)). Qed.
Lemma lem8216535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8216536 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term242 A B C P a b p lt2 s h) = (term242 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8216535) (@lem8216534 A B C P a b p lt2 s h)). Qed.
Lemma lem8216537 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term325 A B C P p lt2 s a b f h g a') = (term325 A B C P p lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216536 A B C P a b p lt2 s h) (@lem8216486 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8216538 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term327 A B C P lt2 s a b f h g a') = (term327 A B C P lt2 s a b f h g a').
Proof. exact (fun_ext (fun p : type560 B C P => @lem8216537 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8216539 {B C P : Type'} : (@all ((B -> C) -> P -> Prop)) = (@all ((B -> C) -> P -> Prop)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> Prop))). Qed.
Lemma lem8216540 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term329 A B C P lt2 s a b f h g a') = (term329 A B C P lt2 s a b f h g a').
Proof. exact (MK_COMB (@lem8216539 B C P) (@lem8216538 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8216541 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term331 A B C P s a b f h g a') = (term331 A B C P s a b f h g a').
Proof. exact (fun_ext (fun lt2 : type1470 A B => @lem8216540 A B C P lt2 s a b f h g a')). Qed.
Lemma lem8216542 {A B : Type'} : (@all (B -> A -> Prop)) = (@all (B -> A -> Prop)).
Proof. exact (eq_refl (@all (B -> A -> Prop))). Qed.
Lemma lem8216543 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term333 A B C P s a b f h g a') = (term333 A B C P s a b f h g a').
Proof. exact (MK_COMB (@lem8216542 A B) (@lem8216541 A B C P s a b f h g a')). Qed.
Lemma lem8216544 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term335 A B C P a b f h g a') = (term335 A B C P a b f h g a').
Proof. exact (fun_ext (fun s : P -> A => @lem8216543 A B C P s a b f h g a')). Qed.
Lemma lem8216545 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8216546 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term337 A B C P a b f h g a') = (term337 A B C P a b f h g a').
Proof. exact (MK_COMB (@lem8216545 A P) (@lem8216544 A B C P a b f h g a')). Qed.
Lemma lem8216547 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term339 A B C P b f h g a') = (term339 A B C P b f h g a').
Proof. exact (fun_ext (fun a : P -> nat => @lem8216546 A B C P a b f h g a')). Qed.
Lemma lem8216548 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8216549 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term341 A B C P b f h g a') = (term341 A B C P b f h g a').
Proof. exact (MK_COMB (@lem8216548 P) (@lem8216547 A B C P b f h g a')). Qed.
Lemma lem8216550 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term343 A B C P f h g a') = (term343 A B C P f h g a').
Proof. exact (fun_ext (fun b : P -> nat => @lem8216549 A B C P b f h g a')). Qed.
Lemma lem8216551 {P : Type'} : (@all (P -> nat)) = (@all (P -> nat)).
Proof. exact (eq_refl (@all (P -> nat))). Qed.
Lemma lem8216552 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term345 A B C P f h g a') = (term345 A B C P f h g a').
Proof. exact (MK_COMB (@lem8216551 P) (@lem8216550 A B C P f h g a')). Qed.
Lemma lem8216553 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (term347 A B C P h g a') = (term347 A B C P h g a').
Proof. exact (fun_ext (fun f : B -> C => @lem8216552 A B C P f h g a')). Qed.
Lemma lem8216554 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216555 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (term349 A B C P h g a') = (term349 A B C P h g a').
Proof. exact (MK_COMB (@lem8216554 B C) (@lem8216553 A B C P h g a')). Qed.
Lemma lem8216556 {A B C P : Type'} (g : B -> C) (a' : P) : (term351 A B C P g a') = (term351 A B C P g a').
Proof. exact (fun_ext (fun h : type555 B C P => @lem8216555 A B C P h g a')). Qed.
Lemma lem8216557 {B C P : Type'} : (@all ((B -> C) -> P -> nat -> nat)) = (@all ((B -> C) -> P -> nat -> nat)).
Proof. exact (eq_refl (@all ((B -> C) -> P -> nat -> nat))). Qed.
Lemma lem8216558 {A B C P : Type'} (g : B -> C) (a' : P) : (term353 A B C P g a') = (term353 A B C P g a').
Proof. exact (MK_COMB (@lem8216557 B C P) (@lem8216556 A B C P g a')). Qed.
Lemma lem8216559 {A B C P : Type'} (a' : P) : (term355 A B C P a') = (term355 A B C P a').
Proof. exact (fun_ext (fun g : B -> C => @lem8216558 A B C P g a')). Qed.
Lemma lem8216560 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216561 {A B C P : Type'} (a' : P) : (term357 A B C P a') = (term357 A B C P a').
Proof. exact (MK_COMB (@lem8216560 B C) (@lem8216559 A B C P a')). Qed.
Lemma lem8216562 {A B C P : Type'} : (term359 A B C P) = (term359 A B C P).
Proof. exact (fun_ext (fun a' : P => @lem8216561 A B C P a')). Qed.
Lemma lem8216563 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216564 {A B C P : Type'} : (term361 A B C P) = (term361 A B C P).
Proof. exact (MK_COMB (@lem8216563 P) (@lem8216562 A B C P)). Qed.
Lemma lem8216693 {A B C P : Type'} : (term360 A B C P) = (term361 A B C P).
Proof. exact (TRANS (@lem8216455 A B C P) (@lem8216564 A B C P)). Qed.
Lemma lem8216694 {A B C P : Type'} : (term361 A B C P) = (term360 A B C P).
Proof. exact (SYM (@lem8216693 A B C P)). Qed.
Lemma lem8216695 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term240 A B C P a b p lt2 s h.
Proof. exact (h1). Qed.
Lemma lem8216698 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term174 A B C P lt2 s a' f g.
Proof. exact (h1). Qed.
Lemma lem8216701 (p : Prop) : p = (term307 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8216702 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : ((h f a' i) = (h g a' i)) = (term364 B C P f h g a' i).
Proof. exact (@lem8216701 ((h f a' i) = (h g a' i))). Qed.
Lemma lem8216703 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (term364 B C P f h g a' i) = ((h f a' i) = (h g a' i)).
Proof. exact (SYM (@lem8216702 B C P f h g a' i)). Qed.
Lemma lem8216704 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term365 B C P f h g a' i.
Proof. exact (h1). Qed.
Lemma lem8216712 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term366 B C P p1 b p f p2) = (term367 B C P p1 b p f p2).
Proof. exact (@lem17045 (term368 P p1 b p2) (p f p2)). Qed.
Lemma lem8216714 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term369 P a p2 p1).
Proof. exact (eq_refl (term369 P a p2 p1)). Qed.
Lemma lem8216715 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term370 B C P a p1 b p f p2) = (term371 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8216714 P a p2 p1) (@lem8216712 B C P p1 b p f p2)). Qed.
Lemma lem8216716 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term372 B C P a p1 b p f p2) = (term370 B C P a p1 b p f p2).
Proof. exact (@lem17045 (term373 P a p2 p1) (term374 B C P p1 b p f p2)). Qed.
Lemma lem8216717 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term372 B C P a p1 b p f p2) = (term371 B C P a p1 b p f p2).
Proof. exact (TRANS (@lem8216716 B C P a p1 b p f p2) (@lem8216715 B C P a p1 b p f p2)). Qed.
Lemma lem8216725 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term366 B C P p1 b p g p2) = (term367 B C P p1 b p g p2).
Proof. exact (@lem17045 (term368 P p1 b p2) (p g p2)). Qed.
Lemma lem8216727 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term369 P a p2 p1).
Proof. exact (eq_refl (term369 P a p2 p1)). Qed.
Lemma lem8216728 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term370 B C P a p1 b p g p2) = (term371 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8216727 P a p2 p1) (@lem8216725 B C P p1 b p g p2)). Qed.
Lemma lem8216729 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term372 B C P a p1 b p g p2) = (term370 B C P a p1 b p g p2).
Proof. exact (@lem17045 (term373 P a p2 p1) (term374 B C P p1 b p g p2)). Qed.
Lemma lem8216730 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term372 B C P a p1 b p g p2) = (term371 B C P a p1 b p g p2).
Proof. exact (TRANS (@lem8216729 B C P a p1 b p g p2) (@lem8216728 B C P a p1 b p g p2)). Qed.
Lemma lem8216737 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term375 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (@lem17362 (term166 A B P lt2 z s p2) ((f z) = (g z))). Qed.
Lemma lem8216738 {B : Type'} (P : B -> Prop) : (term377 B P) = (term378 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem8216739 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term379 A B C P lt2 s p2 f g) = (term380 A B C P lt2 s p2 f g).
Proof. exact (@lem8216738 B (term172 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216740 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term381 A B C P lt2 s p2 f g z) = (term170 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term381 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216741 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8216742 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term382 A B C P lt2 s p2 f g z) = (term375 A B C P lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8216741) (@lem8216740 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216743 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term382 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (TRANS (@lem8216742 A B C P lt2 s p2 f g z) (@lem8216737 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216744 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term383 A B C P lt2 s p2 f g) = (term384 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8216743 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216745 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216746 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term380 A B C P lt2 s p2 f g) = (term385 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216745 B) (@lem8216744 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216747 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term379 A B C P lt2 s p2 f g) = (term385 A B C P lt2 s p2 f g).
Proof. exact (TRANS (@lem8216739 A B C P lt2 s p2 f g) (@lem8216746 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8216749 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term386 B C P a p1 b p g p2) = (term387 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8216748) (@lem8216730 B C P a p1 b p g p2)). Qed.
Lemma lem8216750 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term388 A B C P a p1 b p lt2 s p2 f g) = (term389 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216749 B C P a p1 b p g p2) (@lem8216747 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216751 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term390 A B C P a p1 b p lt2 s p2 f g) = (term388 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem17045 (term96 B C P a p1 b p g p2) (term174 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216752 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term390 A B C P a p1 b p lt2 s p2 f g) = (term389 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (TRANS (@lem8216751 A B C P a p1 b p lt2 s p2 f g) (@lem8216750 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8216754 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term386 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8216753) (@lem8216717 B C P a p1 b p f p2)). Qed.
Lemma lem8216755 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term391 A B C P a p1 b p lt2 s p2 f g) = (term392 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216754 B C P a p1 b p f p2) (@lem8216752 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216756 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term393 A B C P a p1 b p lt2 s p2 f g) = (term391 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem17045 (term96 B C P a p1 b p f p2) (term176 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216757 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term393 A B C P a p1 b p lt2 s p2 f g) = (term392 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (TRANS (@lem8216756 A B C P a p1 b p lt2 s p2 f g) (@lem8216755 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216758 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8216759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8216760 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term394 A B C P a p1 b p lt2 s p2 f g) = (term395 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216759) (@lem8216757 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216761 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term396 A B C P a b p lt2 s f h g p2 p1) = (term397 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8216760 A B C P a p1 b p lt2 s p2 f g) (@lem8216758 B C P f h g p2 p1)). Qed.
Lemma lem8216762 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term229 A B C P a b p lt2 s f h g p2 p1) = (term396 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (@lem17265 (term178 A B C P a p1 b p lt2 s p2 f g) ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8216763 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term229 A B C P a b p lt2 s f h g p2 p1) = (term397 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (TRANS (@lem8216762 A B C P a b p lt2 s f h g p2 p1) (@lem8216761 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216764 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term230 A B C P a b p lt2 s f h g p1) = (term398 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8216763 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216765 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216766 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term231 A B C P a b p lt2 s f h g p1) = (term399 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8216765 P) (@lem8216764 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216767 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term232 A B C P a b p lt2 s f h g) = (term400 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8216766 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8216769 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term233 A B C P a b p lt2 s f h g) = (term401 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8216768) (@lem8216767 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216770 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term235 A B C P a b p lt2 s f h) = (term402 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8216769 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216771 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216772 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term237 A B C P a b p lt2 s f h) = (term403 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8216771 B C) (@lem8216770 A B C P a b p lt2 s f h)). Qed.
Lemma lem8216773 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term239 A B C P a b p lt2 s h) = (term404 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8216772 A B C P a b p lt2 s f h)). Qed.
Lemma lem8216774 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8216775 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term240 A B C P a b p lt2 s h) = (term405 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8216774 B C) (@lem8216773 A B C P a b p lt2 s h)). Qed.
Lemma lem8216886 {A : Type'} (P : Prop) (Q : A -> Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8216887 {B : Type'} (P : Prop) (Q : B -> Prop) : (term406 B P Q) = (term407 B P Q).
Proof. exact (@lem8216886 B P Q). Qed.
Lemma lem8216888 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term408 A B C P a p1 b p lt2 s p2 f g) = (term409 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem8216887 B (term371 B C P a p1 b p g p2) (term384 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216889 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term410 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term410 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216890 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term411 A B C P lt2 s p2 f g) = (term384 A B C P lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8216889 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216891 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216892 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term412 A B C P lt2 s p2 f g) = (term385 A B C P lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216891 B) (@lem8216890 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216893 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term387 B C P a p1 b p g p2) = (term387 B C P a p1 b p g p2).
Proof. exact (eq_refl (term387 B C P a p1 b p g p2)). Qed.
Lemma lem8216894 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term408 A B C P a p1 b p lt2 s p2 f g) = (term389 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216893 B C P a p1 b p g p2) (@lem8216892 A B C P lt2 s p2 f g)). Qed.
Lemma lem8216895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8216896 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term413 A B C P a p1 b p lt2 s p2 f g) = (term414 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216895) (@lem8216894 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216897 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term410 A B C P lt2 s p2 f g z) = (term376 A B C P lt2 s p2 f g z).
Proof. exact (eq_refl (term410 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216898 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term387 B C P a p1 b p g p2) = (term387 B C P a p1 b p g p2).
Proof. exact (eq_refl (term387 B C P a p1 b p g p2)). Qed.
Lemma lem8216899 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term415 A B C P a p1 b p lt2 s p2 f g z) = (term416 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8216898 B C P a p1 b p g p2) (@lem8216897 A B C P lt2 s p2 f g z)). Qed.
Lemma lem8216900 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term417 A B C P a p1 b p lt2 s p2 f g) = (term418 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8216899 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216901 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216902 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term409 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216901 B) (@lem8216900 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216903 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : ((term408 A B C P a p1 b p lt2 s p2 f g) = (term409 A B C P a p1 b p lt2 s p2 f g)) = ((term389 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8216896 A B C P a p1 b p lt2 s p2 f g) (@lem8216902 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216904 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term389 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8216903 A B C P a p1 b p lt2 s p2 f g) (@lem8216888 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216905 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (eq_refl (term387 B C P a p1 b p f p2)). Qed.
Lemma lem8216906 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term392 A B C P a p1 b p lt2 s p2 f g) = (term420 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216905 B C P a p1 b p f p2) (@lem8216904 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216908 {A : Type'} (P : Prop) (Q : A -> Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem8216909 {B : Type'} (P : Prop) (Q : B -> Prop) : (term406 B P Q) = (term407 B P Q).
Proof. exact (@lem8216908 B P Q). Qed.
Lemma lem8216910 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term421 A B C P a p1 b p lt2 s p2 f g) = (term422 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (@lem8216909 B (term371 B C P a p1 b p f p2) (term418 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216911 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term423 A B C P a p1 b p lt2 s p2 f g z) = (term416 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term423 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216912 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term424 A B C P a p1 b p lt2 s p2 f g) = (term418 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8216911 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216913 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216914 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term425 A B C P a p1 b p lt2 s p2 f g) = (term419 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216913 B) (@lem8216912 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216915 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (eq_refl (term387 B C P a p1 b p f p2)). Qed.
Lemma lem8216916 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term421 A B C P a p1 b p lt2 s p2 f g) = (term420 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216915 B C P a p1 b p f p2) (@lem8216914 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8216918 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term426 A B C P a p1 b p lt2 s p2 f g) = (term427 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216917) (@lem8216916 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216919 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term423 A B C P a p1 b p lt2 s p2 f g z) = (term416 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term423 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216920 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term387 B C P a p1 b p f p2).
Proof. exact (eq_refl (term387 B C P a p1 b p f p2)). Qed.
Lemma lem8216921 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term428 A B C P a p1 b p lt2 s p2 f g z) = (term429 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8216920 B C P a p1 b p f p2) (@lem8216919 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216922 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term430 A B C P a p1 b p lt2 s p2 f g) = (term431 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8216921 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216923 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216924 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term422 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216923 B) (@lem8216922 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216925 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : ((term421 A B C P a p1 b p lt2 s p2 f g) = (term422 A B C P a p1 b p lt2 s p2 f g)) = ((term420 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g)).
Proof. exact (MK_COMB (@lem8216918 A B C P a p1 b p lt2 s p2 f g) (@lem8216924 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216926 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term420 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (EQ_MP (@lem8216925 A B C P a p1 b p lt2 s p2 f g) (@lem8216910 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216927 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term392 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (TRANS (@lem8216906 A B C P a p1 b p lt2 s p2 f g) (@lem8216926 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8216929 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term395 A B C P a p1 b p lt2 s p2 f g) = (term433 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216928) (@lem8216927 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216930 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8216931 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term397 A B C P a b p lt2 s f h g p2 p1) = (term434 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8216929 A B C P a p1 b p lt2 s p2 f g) (@lem8216930 B C P f h g p2 p1)). Qed.
Lemma lem8216933 {A : Type'} (P : A -> Prop) (Q : Prop) : (term435 A P Q) = (term436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8216934 {B : Type'} (P : B -> Prop) (Q : Prop) : (term435 B P Q) = (term436 B P Q).
Proof. exact (@lem8216933 B P Q). Qed.
Lemma lem8216935 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term437 A B C P a b p lt2 s f h g p2 p1) = (term438 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (@lem8216934 B (term431 A B C P a p1 b p lt2 s p2 f g) ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8216936 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term439 A B C P a p1 b p lt2 s p2 f g z) = (term429 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term439 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216937 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term440 A B C P a p1 b p lt2 s p2 f g) = (term431 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (fun_ext (fun z : B => @lem8216936 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216938 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216939 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term441 A B C P a p1 b p lt2 s p2 f g) = (term432 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216938 B) (@lem8216937 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216940 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8216941 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) : (term442 A B C P a p1 b p lt2 s p2 f g) = (term433 A B C P a p1 b p lt2 s p2 f g).
Proof. exact (MK_COMB (@lem8216940) (@lem8216939 A B C P a p1 b p lt2 s p2 f g)). Qed.
Lemma lem8216942 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8216943 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term437 A B C P a b p lt2 s f h g p2 p1) = (term434 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8216941 A B C P a p1 b p lt2 s p2 f g) (@lem8216942 B C P f h g p2 p1)). Qed.
Lemma lem8216944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8216945 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term443 A B C P a b p lt2 s f h g p2 p1) = (term444 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8216944) (@lem8216943 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216946 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term439 A B C P a p1 b p lt2 s p2 f g z) = (term429 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (eq_refl (term439 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8216948 {A B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (p2 : P) (f : B -> C) (g : B -> C) (z : B) : (term445 A B C P a p1 b p lt2 s p2 f g z) = (term446 A B C P a p1 b p lt2 s p2 f g z).
Proof. exact (MK_COMB (@lem8216947) (@lem8216946 A B C P a p1 b p lt2 s p2 f g z)). Qed.
Lemma lem8216949 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((h f p2 p1) = (h g p2 p1)).
Proof. exact (eq_refl ((h f p2 p1) = (h g p2 p1))). Qed.
Lemma lem8216950 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term447 A B C P a b p lt2 s z f h g p2 p1) = (term448 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (MK_COMB (@lem8216948 A B C P a p1 b p lt2 s p2 f g z) (@lem8216949 B C P f h g p2 p1)). Qed.
Lemma lem8216951 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term449 A B C P a b p lt2 s f h g p2 p1) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (fun_ext (fun z : B => @lem8216950 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8216952 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216953 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term438 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8216952 B) (@lem8216951 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216954 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((term437 A B C P a b p lt2 s f h g p2 p1) = (term438 A B C P a b p lt2 s f h g p2 p1)) = ((term434 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1)).
Proof. exact (MK_COMB (@lem8216945 A B C P a b p lt2 s f h g p2 p1) (@lem8216953 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216955 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term434 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (EQ_MP (@lem8216954 A B C P a b p lt2 s f h g p2 p1) (@lem8216935 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216956 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term397 A B C P a b p lt2 s f h g p2 p1) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (TRANS (@lem8216931 A B C P a b p lt2 s f h g p2 p1) (@lem8216955 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216957 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term398 A B C P a b p lt2 s f h g p1) = (term452 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8216956 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216958 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216959 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term399 A B C P a b p lt2 s f h g p1) = (term453 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8216958 P) (@lem8216957 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216961 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8216962 {B P : Type'} (P' : type1470 B P) : (term456 B P P') = (term457 B P P').
Proof. exact (@lem8216961 P B P'). Qed.
Lemma lem8216963 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term458 A B C P a b p lt2 s f h g p1) = (term459 A B C P a b p lt2 s f h g p1).
Proof. exact (@lem8216962 B P (term460 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216964 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term461 A B C P a b p lt2 s f h g p1 p2) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (eq_refl (term461 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8216965 {B : Type'} (z : B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8216966 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) (z : B) : (term462 A B C P a b p lt2 s f h g p1 p2 z) = (term463 A B C P a b p lt2 s f h g p2 p1 z).
Proof. exact (MK_COMB (@lem8216964 A B C P a b p lt2 s f h g p2 p1) (@lem8216965 B z)). Qed.
Lemma lem8216967 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term463 A B C P a b p lt2 s f h g p2 p1 z) = (term448 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (eq_refl (term463 A B C P a b p lt2 s f h g p2 p1 z)). Qed.
Lemma lem8216968 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term462 A B C P a b p lt2 s f h g p1 p2 z) = (term448 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (TRANS (@lem8216966 A B C P a b p lt2 s f h g p2 p1 z) (@lem8216967 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8216969 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term464 A B C P a b p lt2 s f h g p1 p2) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (fun_ext (fun z : B => @lem8216968 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8216970 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem8216971 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term465 A B C P a b p lt2 s f h g p1 p2) = (term451 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (MK_COMB (@lem8216970 B) (@lem8216969 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216972 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term466 A B C P a b p lt2 s f h g p1) = (term452 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8216971 A B C P a b p lt2 s f h g p2 p1)). Qed.
Lemma lem8216973 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216974 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term458 A B C P a b p lt2 s f h g p1) = (term453 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8216973 P) (@lem8216972 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8216976 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term467 A B C P a b p lt2 s f h g p1) = (term468 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8216975) (@lem8216974 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216977 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term461 A B C P a b p lt2 s f h g p1 p2) = (term450 A B C P a b p lt2 s f h g p2 p1).
Proof. exact (eq_refl (term461 A B C P a b p lt2 s f h g p1 p2)). Qed.
Lemma lem8216978 {B P : Type'} (z : P -> B) (p2 : P) : (z p2) = (z p2).
Proof. exact (eq_refl (z p2)). Qed.
Lemma lem8216979 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) (z : P -> B) (p2 : P) : (term469 A B C P a b p lt2 s f h g p1 z p2) = (term470 A B C P a b p lt2 s f h g p1 z p2).
Proof. exact (MK_COMB (@lem8216977 A B C P a b p lt2 s f h g p2 p1) (@lem8216978 B P z p2)). Qed.
Lemma lem8216980 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term470 A B C P a b p lt2 s f h g p1 z p2) = (term471 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (eq_refl (term470 A B C P a b p lt2 s f h g p1 z p2)). Qed.
Lemma lem8216981 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term469 A B C P a b p lt2 s f h g p1 z p2) = (term471 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (TRANS (@lem8216979 A B C P a b p lt2 s f h g p1 z p2) (@lem8216980 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8216982 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term472 A B C P a b p lt2 s f h g p1 z) = (term473 A B C P a b p lt2 s z f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8216981 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8216983 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8216984 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term474 A B C P a b p lt2 s f h g p1 z) = (term475 A B C P a b p lt2 s z f h g p1).
Proof. exact (MK_COMB (@lem8216983 P) (@lem8216982 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8216985 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term476 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun z : P -> B => @lem8216984 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8216986 {B P : Type'} : (@ex (P -> B)) = (@ex (P -> B)).
Proof. exact (eq_refl (@ex (P -> B))). Qed.
Lemma lem8216987 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term459 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8216986 B P) (@lem8216985 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216988 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : ((term458 A B C P a b p lt2 s f h g p1) = (term459 A B C P a b p lt2 s f h g p1)) = ((term453 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1)).
Proof. exact (MK_COMB (@lem8216976 A B C P a b p lt2 s f h g p1) (@lem8216987 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216989 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term453 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (EQ_MP (@lem8216988 A B C P a b p lt2 s f h g p1) (@lem8216963 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216990 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term399 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (TRANS (@lem8216959 A B C P a b p lt2 s f h g p1) (@lem8216989 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216991 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term400 A B C P a b p lt2 s f h g) = (term479 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8216990 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216992 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8216993 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term401 A B C P a b p lt2 s f h g) = (term480 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8216992) (@lem8216991 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216995 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8216996 {B P : Type'} (P' : type1579 B P) : (term481 B P P') = (term482 B P P').
Proof. exact (@lem8216995 nat (P -> B) P'). Qed.
Lemma lem8216997 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term483 A B C P a b p lt2 s f h g) = (term484 A B C P a b p lt2 s f h g).
Proof. exact (@lem8216996 B P (term485 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8216998 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term486 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (eq_refl (term486 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8216999 {B P : Type'} (z : P -> B) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8217000 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) (z : P -> B) : (term487 A B C P a b p lt2 s f h g p1 z) = (term488 A B C P a b p lt2 s f h g p1 z).
Proof. exact (MK_COMB (@lem8216998 A B C P a b p lt2 s f h g p1) (@lem8216999 B P z)). Qed.
Lemma lem8217001 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term488 A B C P a b p lt2 s f h g p1 z) = (term475 A B C P a b p lt2 s z f h g p1).
Proof. exact (eq_refl (term488 A B C P a b p lt2 s f h g p1 z)). Qed.
Lemma lem8217002 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : P -> B) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term487 A B C P a b p lt2 s f h g p1 z) = (term475 A B C P a b p lt2 s z f h g p1).
Proof. exact (TRANS (@lem8217000 A B C P a b p lt2 s f h g p1 z) (@lem8217001 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8217003 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term489 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (fun_ext (fun z : P -> B => @lem8217002 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8217004 {B P : Type'} : (@ex (P -> B)) = (@ex (P -> B)).
Proof. exact (eq_refl (@ex (P -> B))). Qed.
Lemma lem8217005 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term490 A B C P a b p lt2 s f h g p1) = (term478 A B C P a b p lt2 s f h g p1).
Proof. exact (MK_COMB (@lem8217004 B P) (@lem8217003 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8217006 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term491 A B C P a b p lt2 s f h g) = (term479 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8217005 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8217007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8217008 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term483 A B C P a b p lt2 s f h g) = (term480 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8217007) (@lem8217006 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8217010 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term492 A B C P a b p lt2 s f h g) = (term493 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8217009) (@lem8217008 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217011 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term486 A B C P a b p lt2 s f h g p1) = (term477 A B C P a b p lt2 s f h g p1).
Proof. exact (eq_refl (term486 A B C P a b p lt2 s f h g p1)). Qed.
Lemma lem8217012 {B P : Type'} (z : type1599 B P) (p1 : nat) : (z p1) = (z p1).
Proof. exact (eq_refl (z p1)). Qed.
Lemma lem8217013 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (z : type1599 B P) (p1 : nat) : (term494 A B C P a b p lt2 s f h g z p1) = (term495 A B C P a b p lt2 s f h g z p1).
Proof. exact (MK_COMB (@lem8217011 A B C P a b p lt2 s f h g p1) (@lem8217012 B P z p1)). Qed.
Lemma lem8217014 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term495 A B C P a b p lt2 s f h g z p1) = (term496 A B C P a b p lt2 s z f h g p1).
Proof. exact (eq_refl (term495 A B C P a b p lt2 s f h g z p1)). Qed.
Lemma lem8217015 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term494 A B C P a b p lt2 s f h g z p1) = (term496 A B C P a b p lt2 s z f h g p1).
Proof. exact (TRANS (@lem8217013 A B C P a b p lt2 s f h g z p1) (@lem8217014 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8217016 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term497 A B C P a b p lt2 s f h g z) = (term498 A B C P a b p lt2 s z f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8217015 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8217017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8217018 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term499 A B C P a b p lt2 s f h g z) = (term500 A B C P a b p lt2 s z f h g).
Proof. exact (MK_COMB (@lem8217017) (@lem8217016 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217019 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term501 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun z : type1599 B P => @lem8217018 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217020 {B P : Type'} : (@ex (nat -> P -> B)) = (@ex (nat -> P -> B)).
Proof. exact (eq_refl (@ex (nat -> P -> B))). Qed.
Lemma lem8217021 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term484 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8217020 B P) (@lem8217019 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217022 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : ((term483 A B C P a b p lt2 s f h g) = (term484 A B C P a b p lt2 s f h g)) = ((term480 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g)).
Proof. exact (MK_COMB (@lem8217010 A B C P a b p lt2 s f h g) (@lem8217021 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217023 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term480 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (EQ_MP (@lem8217022 A B C P a b p lt2 s f h g) (@lem8216997 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217024 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term401 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (TRANS (@lem8216993 A B C P a b p lt2 s f h g) (@lem8217023 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217025 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term402 A B C P a b p lt2 s f h) = (term504 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8217024 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217026 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217027 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term403 A B C P a b p lt2 s f h) = (term505 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8217026 B C) (@lem8217025 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217029 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8217030 {B C P : Type'} (P' : type539 B C P) : (term506 B C P P') = (term507 B C P P').
Proof. exact (@lem8217029 (B -> C) (type1599 B P) P'). Qed.
Lemma lem8217031 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term508 A B C P a b p lt2 s f h) = (term509 A B C P a b p lt2 s f h).
Proof. exact (@lem8217030 B C P (term510 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217032 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term511 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (eq_refl (term511 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217033 {B P : Type'} (z : type1599 B P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8217034 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) (z : type1599 B P) : (term512 A B C P a b p lt2 s f h g z) = (term513 A B C P a b p lt2 s f h g z).
Proof. exact (MK_COMB (@lem8217032 A B C P a b p lt2 s f h g) (@lem8217033 B P z)). Qed.
Lemma lem8217035 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term513 A B C P a b p lt2 s f h g z) = (term500 A B C P a b p lt2 s z f h g).
Proof. exact (eq_refl (term513 A B C P a b p lt2 s f h g z)). Qed.
Lemma lem8217036 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type1599 B P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term512 A B C P a b p lt2 s f h g z) = (term500 A B C P a b p lt2 s z f h g).
Proof. exact (TRANS (@lem8217034 A B C P a b p lt2 s f h g z) (@lem8217035 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217037 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term514 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (fun_ext (fun z : type1599 B P => @lem8217036 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217038 {B P : Type'} : (@ex (nat -> P -> B)) = (@ex (nat -> P -> B)).
Proof. exact (eq_refl (@ex (nat -> P -> B))). Qed.
Lemma lem8217039 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term515 A B C P a b p lt2 s f h g) = (term503 A B C P a b p lt2 s f h g).
Proof. exact (MK_COMB (@lem8217038 B P) (@lem8217037 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217040 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term516 A B C P a b p lt2 s f h) = (term504 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8217039 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217041 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217042 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term508 A B C P a b p lt2 s f h) = (term505 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8217041 B C) (@lem8217040 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217043 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8217044 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term517 A B C P a b p lt2 s f h) = (term518 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8217043) (@lem8217042 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217045 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term511 A B C P a b p lt2 s f h g) = (term502 A B C P a b p lt2 s f h g).
Proof. exact (eq_refl (term511 A B C P a b p lt2 s f h g)). Qed.
Lemma lem8217046 {B C P : Type'} (z : type567 B C P) (g : B -> C) : (z g) = (z g).
Proof. exact (eq_refl (z g)). Qed.
Lemma lem8217047 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (z : type567 B C P) (g : B -> C) : (term519 A B C P a b p lt2 s f h z g) = (term520 A B C P a b p lt2 s f h z g).
Proof. exact (MK_COMB (@lem8217045 A B C P a b p lt2 s f h g) (@lem8217046 B C P z g)). Qed.
Lemma lem8217048 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term520 A B C P a b p lt2 s f h z g) = (term521 A B C P a b p lt2 s z f h g).
Proof. exact (eq_refl (term520 A B C P a b p lt2 s f h z g)). Qed.
Lemma lem8217049 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term519 A B C P a b p lt2 s f h z g) = (term521 A B C P a b p lt2 s z f h g).
Proof. exact (TRANS (@lem8217047 A B C P a b p lt2 s f h z g) (@lem8217048 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217050 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type555 B C P) : (term522 A B C P a b p lt2 s f h z) = (term523 A B C P a b p lt2 s z f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8217049 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217051 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217052 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type555 B C P) : (term524 A B C P a b p lt2 s f h z) = (term525 A B C P a b p lt2 s z f h).
Proof. exact (MK_COMB (@lem8217051 B C) (@lem8217050 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217053 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term526 A B C P a b p lt2 s f h) = (term527 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun z : type567 B C P => @lem8217052 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217054 {B C P : Type'} : (@ex ((B -> C) -> nat -> P -> B)) = (@ex ((B -> C) -> nat -> P -> B)).
Proof. exact (eq_refl (@ex ((B -> C) -> nat -> P -> B))). Qed.
Lemma lem8217055 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term509 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8217054 B C P) (@lem8217053 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217056 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : ((term508 A B C P a b p lt2 s f h) = (term509 A B C P a b p lt2 s f h)) = ((term505 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h)).
Proof. exact (MK_COMB (@lem8217044 A B C P a b p lt2 s f h) (@lem8217055 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217057 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term505 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h).
Proof. exact (EQ_MP (@lem8217056 A B C P a b p lt2 s f h) (@lem8217031 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217058 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term403 A B C P a b p lt2 s f h) = (term528 A B C P a b p lt2 s f h).
Proof. exact (TRANS (@lem8217027 A B C P a b p lt2 s f h) (@lem8217057 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217059 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term404 A B C P a b p lt2 s h) = (term529 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8217058 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217060 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217061 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term405 A B C P a b p lt2 s h) = (term530 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8217060 B C) (@lem8217059 A B C P a b p lt2 s h)). Qed.
Lemma lem8217063 {A B : Type'} (P : type1413 A B) : (term454 A B P) = (term455 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem8217064 {B C P : Type'} (P' : type498 B C P) : (term531 B C P P') = (term532 B C P P').
Proof. exact (@lem8217063 (B -> C) (type567 B C P) P'). Qed.
Lemma lem8217065 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term533 A B C P a b p lt2 s h) = (term534 A B C P a b p lt2 s h).
Proof. exact (@lem8217064 B C P (term535 A B C P a b p lt2 s h)). Qed.
Lemma lem8217066 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term536 A B C P a b p lt2 s h f) = (term527 A B C P a b p lt2 s f h).
Proof. exact (eq_refl (term536 A B C P a b p lt2 s h f)). Qed.
Lemma lem8217067 {B C P : Type'} (z : type567 B C P) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem8217068 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) (z : type567 B C P) : (term537 A B C P a b p lt2 s h f z) = (term538 A B C P a b p lt2 s f h z).
Proof. exact (MK_COMB (@lem8217066 A B C P a b p lt2 s f h) (@lem8217067 B C P z)). Qed.
Lemma lem8217069 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type555 B C P) : (term538 A B C P a b p lt2 s f h z) = (term525 A B C P a b p lt2 s z f h).
Proof. exact (eq_refl (term538 A B C P a b p lt2 s f h z)). Qed.
Lemma lem8217070 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type567 B C P) (f : B -> C) (h : type555 B C P) : (term537 A B C P a b p lt2 s h f z) = (term525 A B C P a b p lt2 s z f h).
Proof. exact (TRANS (@lem8217068 A B C P a b p lt2 s f h z) (@lem8217069 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217071 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term539 A B C P a b p lt2 s h f) = (term527 A B C P a b p lt2 s f h).
Proof. exact (fun_ext (fun z : type567 B C P => @lem8217070 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217072 {B C P : Type'} : (@ex ((B -> C) -> nat -> P -> B)) = (@ex ((B -> C) -> nat -> P -> B)).
Proof. exact (eq_refl (@ex ((B -> C) -> nat -> P -> B))). Qed.
Lemma lem8217073 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term540 A B C P a b p lt2 s h f) = (term528 A B C P a b p lt2 s f h).
Proof. exact (MK_COMB (@lem8217072 B C P) (@lem8217071 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217074 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term541 A B C P a b p lt2 s h) = (term529 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun f : B -> C => @lem8217073 A B C P a b p lt2 s f h)). Qed.
Lemma lem8217075 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217076 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term533 A B C P a b p lt2 s h) = (term530 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8217075 B C) (@lem8217074 A B C P a b p lt2 s h)). Qed.
Lemma lem8217077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8217078 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term542 A B C P a b p lt2 s h) = (term543 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8217077) (@lem8217076 A B C P a b p lt2 s h)). Qed.
Lemma lem8217079 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (h : type555 B C P) : (term536 A B C P a b p lt2 s h f) = (term527 A B C P a b p lt2 s f h).
Proof. exact (eq_refl (term536 A B C P a b p lt2 s h f)). Qed.
Lemma lem8217080 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (z f).
Proof. exact (eq_refl (z f)). Qed.
Lemma lem8217081 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (z : type521 B C P) (f : B -> C) : (term544 A B C P a b p lt2 s h z f) = (term545 A B C P a b p lt2 s h z f).
Proof. exact (MK_COMB (@lem8217079 A B C P a b p lt2 s f h) (@lem8217080 B C P z f)). Qed.
Lemma lem8217082 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) : (term545 A B C P a b p lt2 s h z f) = (term546 A B C P a b p lt2 s z f h).
Proof. exact (eq_refl (term545 A B C P a b p lt2 s h z f)). Qed.
Lemma lem8217083 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) : (term544 A B C P a b p lt2 s h z f) = (term546 A B C P a b p lt2 s z f h).
Proof. exact (TRANS (@lem8217081 A B C P a b p lt2 s h z f) (@lem8217082 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217084 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) : (term547 A B C P a b p lt2 s h z) = (term548 A B C P a b p lt2 s z h).
Proof. exact (fun_ext (fun f : B -> C => @lem8217083 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217085 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217086 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) : (term549 A B C P a b p lt2 s h z) = (term550 A B C P a b p lt2 s z h).
Proof. exact (MK_COMB (@lem8217085 B C) (@lem8217084 A B C P a b p lt2 s z h)). Qed.
Lemma lem8217087 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term551 A B C P a b p lt2 s h) = (term552 A B C P a b p lt2 s h).
Proof. exact (fun_ext (fun z : type521 B C P => @lem8217086 A B C P a b p lt2 s z h)). Qed.
Lemma lem8217088 {B C P : Type'} : (@ex ((B -> C) -> (B -> C) -> nat -> P -> B)) = (@ex ((B -> C) -> (B -> C) -> nat -> P -> B)).
Proof. exact (eq_refl (@ex ((B -> C) -> (B -> C) -> nat -> P -> B))). Qed.
Lemma lem8217089 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term534 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (MK_COMB (@lem8217088 B C P) (@lem8217087 A B C P a b p lt2 s h)). Qed.
Lemma lem8217090 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : ((term533 A B C P a b p lt2 s h) = (term534 A B C P a b p lt2 s h)) = ((term530 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h)).
Proof. exact (MK_COMB (@lem8217078 A B C P a b p lt2 s h) (@lem8217089 A B C P a b p lt2 s h)). Qed.
Lemma lem8217091 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term530 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (EQ_MP (@lem8217090 A B C P a b p lt2 s h) (@lem8217065 A B C P a b p lt2 s h)). Qed.
Lemma lem8217093 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term405 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (TRANS (@lem8217061 A B C P a b p lt2 s h) (@lem8217091 A B C P a b p lt2 s h)). Qed.
Lemma lem8217094 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : (term240 A B C P a b p lt2 s h) = (term553 A B C P a b p lt2 s h).
Proof. exact (TRANS (@lem8216775 A B C P a b p lt2 s h) (@lem8217093 A B C P a b p lt2 s h)). Qed.
Lemma lem8217095 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term553 A B C P a b p lt2 s h.
Proof. exact (EQ_MP (@lem8217094 A B C P a b p lt2 s h) (@lem8216695 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8217101 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : p f a'.
Proof. exact (h1). Qed.
Lemma lem8217107 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : p g a'.
Proof. exact (h1). Qed.
Lemma lem8217114 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term170 A B C P lt2 s a' f g z) = (term554 A B C P lt2 s a' f g z).
Proof. exact (@lem17265 (term166 A B P lt2 z s a') ((f z) = (g z))). Qed.
Lemma lem8217115 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term172 A B C P lt2 s a' f g) = (term555 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8217114 A B C P lt2 s a' f g z)). Qed.
Lemma lem8217116 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8217169 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term174 A B C P lt2 s a' f g) = (term556 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8217116 B) (@lem8217115 A B C P lt2 s a' f g)). Qed.
Lemma lem8217170 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term556 A B C P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8217169 A B C P lt2 s a' f g) (@lem8216698 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8217180 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term557 P a i b a'.
Proof. exact (h1). Qed.
Lemma lem8217186 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term365 B C P f h g a' i.
Proof. exact (h1). Qed.
Lemma lem8217187 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term550 A B C P a b p lt2 s z h.
Proof. exact (h1). Qed.
Lemma lem8217194 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217195 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8217194 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8217196 {B C P : Type'} (p : type560 B C P) (f : B -> C) : (p f) = (@I ((B -> C) -> P -> Prop) p f).
Proof. exact (@lem8217195 B C P p f). Qed.
Lemma lem8217197 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8217198 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (p f a') = (@I ((B -> C) -> P -> Prop) p f a').
Proof. exact (MK_COMB (@lem8217196 B C P p f) (@lem8217197 P a')). Qed.
Lemma lem8217200 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217201 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8217200 P Prop f x). Qed.
Lemma lem8217202 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (@I ((B -> C) -> P -> Prop) p f a') = (term558 B C P p f a').
Proof. exact (@lem8217201 P (@I ((B -> C) -> P -> Prop) p f) a'). Qed.
Lemma lem8217204 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (p f a') = (term558 B C P p f a').
Proof. exact (TRANS (@lem8217198 B C P p f a') (@lem8217202 B C P p f a')). Qed.
Lemma lem8217212 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217213 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8217212 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8217214 {B C P : Type'} (p : type560 B C P) (g : B -> C) : (p g) = (@I ((B -> C) -> P -> Prop) p g).
Proof. exact (@lem8217213 B C P p g). Qed.
Lemma lem8217215 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8217216 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (p g a') = (@I ((B -> C) -> P -> Prop) p g a').
Proof. exact (MK_COMB (@lem8217214 B C P p g) (@lem8217215 P a')). Qed.
Lemma lem8217218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217219 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8217218 P Prop f x). Qed.
Lemma lem8217220 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (@I ((B -> C) -> P -> Prop) p g a') = (term558 B C P p g a').
Proof. exact (@lem8217219 P (@I ((B -> C) -> P -> Prop) p g) a'). Qed.
Lemma lem8217222 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (p g a') = (term558 B C P p g a').
Proof. exact (TRANS (@lem8217216 B C P p g a') (@lem8217220 B C P p g a')). Qed.
Lemma lem8217224 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8217229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217230 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8217229 B C f x). Qed.
Lemma lem8217232 {B C : Type'} (f : B -> C) (z : B) : (f z) = (@I (B -> C) f z).
Proof. exact (@lem8217230 B C f z). Qed.
Lemma lem8217237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217238 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8217237 B C f x). Qed.
Lemma lem8217240 {B C : Type'} (g : B -> C) (z : B) : (g z) = (@I (B -> C) g z).
Proof. exact (@lem8217238 B C g z). Qed.
Lemma lem8217241 {B C : Type'} (f : B -> C) (z : B) : (term559 B C f z) = (term560 B C f z).
Proof. exact (MK_COMB (@lem8217224 C) (@lem8217232 B C f z)). Qed.
Lemma lem8217242 {B C : Type'} (f : B -> C) (g : B -> C) (z : B) : ((f z) = (g z)) = ((@I (B -> C) f z) = (@I (B -> C) g z)).
Proof. exact (MK_COMB (@lem8217241 B C f z) (@lem8217240 B C g z)). Qed.
Lemma lem8217243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217251 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8217250 P A f x). Qed.
Lemma lem8217253 {A P : Type'} (s : P -> A) (a' : P) : (s a') = (@I (P -> A) s a').
Proof. exact (@lem8217251 A P s a'). Qed.
Lemma lem8217254 {A B : Type'} (lt2 : type1470 A B) (z : B) : (lt2 z) = (lt2 z).
Proof. exact (eq_refl (lt2 z)). Qed.
Lemma lem8217255 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term166 A B P lt2 z s a') = (term561 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8217254 A B lt2 z) (@lem8217253 A P s a')). Qed.
Lemma lem8217257 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217258 {A B : Type'} (f : type1470 A B) (x : B) : (f x) = (@I (B -> A -> Prop) f x).
Proof. exact (@lem8217257 B (A -> Prop) f x). Qed.
Lemma lem8217259 {A B : Type'} (lt2 : type1470 A B) (z : B) : (lt2 z) = (@I (B -> A -> Prop) lt2 z).
Proof. exact (@lem8217258 A B lt2 z). Qed.
Lemma lem8217260 {A P : Type'} (s : P -> A) (a' : P) : (@I (P -> A) s a') = (@I (P -> A) s a').
Proof. exact (eq_refl (@I (P -> A) s a')). Qed.
Lemma lem8217261 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term561 A B P lt2 z s a') = (term562 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8217259 A B lt2 z) (@lem8217260 A P s a')). Qed.
Lemma lem8217263 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217264 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8217263 A Prop f x). Qed.
Lemma lem8217265 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term562 A B P lt2 z s a') = (term563 A B P lt2 z s a').
Proof. exact (@lem8217264 A (@I (B -> A -> Prop) lt2 z) (@I (P -> A) s a')). Qed.
Lemma lem8217266 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term561 A B P lt2 z s a') = (term563 A B P lt2 z s a').
Proof. exact (TRANS (@lem8217261 A B P lt2 z s a') (@lem8217265 A B P lt2 z s a')). Qed.
Lemma lem8217267 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term166 A B P lt2 z s a') = (term563 A B P lt2 z s a').
Proof. exact (TRANS (@lem8217255 A B P lt2 z s a') (@lem8217266 A B P lt2 z s a')). Qed.
Lemma lem8217268 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term564 A B P lt2 z s a') = (term565 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8217243) (@lem8217267 A B P lt2 z s a')). Qed.
Lemma lem8217269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217270 {A B P : Type'} (lt2 : type1470 A B) (z : B) (s : P -> A) (a' : P) : (term566 A B P lt2 z s a') = (term567 A B P lt2 z s a').
Proof. exact (MK_COMB (@lem8217269) (@lem8217268 A B P lt2 z s a')). Qed.
Lemma lem8217271 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term554 A B C P lt2 s a' f g z) = (term568 A B C P lt2 s a' f g z).
Proof. exact (MK_COMB (@lem8217270 A B P lt2 z s a') (@lem8217242 B C f g z)). Qed.
Lemma lem8217272 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term555 A B C P lt2 s a' f g) = (term569 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8217271 A B C P lt2 s a' f g z)). Qed.
Lemma lem8217273 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8217274 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term556 A B C P lt2 s a' f g) = (term570 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8217273 B) (@lem8217272 A B C P lt2 s a' f g)). Qed.
Lemma lem8217275 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term570 A B C P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8217274 A B C P lt2 s a' f g) (@lem8217170 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8217282 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217283 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8217282 P nat f x). Qed.
Lemma lem8217285 {P : Type'} (b : P -> nat) (a' : P) : (b a') = (@I (P -> nat) b a').
Proof. exact (@lem8217283 P b a'). Qed.
Lemma lem8217286 (i : nat) : (Peano.le i) = (Peano.le i).
Proof. exact (eq_refl (Peano.le i)). Qed.
Lemma lem8217287 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term368 P i b a') = (term571 P i b a').
Proof. exact (MK_COMB (@lem8217286 i) (@lem8217285 P b a')). Qed.
Lemma lem8217289 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217290 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8217289 nat (nat -> Prop) f x). Qed.
Lemma lem8217291 (i : nat) : (Peano.le i) = (@I (nat -> nat -> Prop) Peano.le i).
Proof. exact (@lem8217290 Peano.le i). Qed.
Lemma lem8217292 {P : Type'} (b : P -> nat) (a' : P) : (@I (P -> nat) b a') = (@I (P -> nat) b a').
Proof. exact (eq_refl (@I (P -> nat) b a')). Qed.
Lemma lem8217293 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term571 P i b a') = (term572 P i b a').
Proof. exact (MK_COMB (@lem8217291 i) (@lem8217292 P b a')). Qed.
Lemma lem8217295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217296 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8217295 nat Prop f x). Qed.
Lemma lem8217297 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term572 P i b a') = (term573 P i b a').
Proof. exact (@lem8217296 (@I (nat -> nat -> Prop) Peano.le i) (@I (P -> nat) b a')). Qed.
Lemma lem8217298 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term571 P i b a') = (term573 P i b a').
Proof. exact (TRANS (@lem8217293 P i b a') (@lem8217297 P i b a')). Qed.
Lemma lem8217299 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term368 P i b a') = (term573 P i b a').
Proof. exact (TRANS (@lem8217287 P i b a') (@lem8217298 P i b a')). Qed.
Lemma lem8217300 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem8217305 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217306 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8217305 P nat f x). Qed.
Lemma lem8217308 {P : Type'} (a : P -> nat) (a' : P) : (a a') = (@I (P -> nat) a a').
Proof. exact (@lem8217306 P a a'). Qed.
Lemma lem8217309 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8217310 {P : Type'} (a : P -> nat) (a' : P) : (term574 P a a') = (term575 P a a').
Proof. exact (MK_COMB (@lem8217300) (@lem8217308 P a a')). Qed.
Lemma lem8217311 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term373 P a a' i) = (term576 P a a' i).
Proof. exact (MK_COMB (@lem8217310 P a a') (@lem8217309 i)). Qed.
Lemma lem8217313 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217314 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8217313 nat (nat -> Prop) f x). Qed.
Lemma lem8217315 {P : Type'} (a : P -> nat) (a' : P) : (term575 P a a') = (term577 P a a').
Proof. exact (@lem8217314 Peano.le (@I (P -> nat) a a')). Qed.
Lemma lem8217316 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8217317 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term576 P a a' i) = (term578 P a a' i).
Proof. exact (MK_COMB (@lem8217315 P a a') (@lem8217316 i)). Qed.
Lemma lem8217319 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217320 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8217319 nat Prop f x). Qed.
Lemma lem8217321 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term578 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8217320 (term577 P a a') i). Qed.
Lemma lem8217322 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term576 P a a' i) = (term579 P a a' i).
Proof. exact (TRANS (@lem8217317 P a a' i) (@lem8217321 P a a' i)). Qed.
Lemma lem8217323 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term373 P a a' i) = (term579 P a a' i).
Proof. exact (TRANS (@lem8217311 P a a' i) (@lem8217322 P a a' i)). Qed.
Lemma lem8217324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8217325 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term580 P a a' i) = (term581 P a a' i).
Proof. exact (MK_COMB (@lem8217324) (@lem8217323 P a a' i)). Qed.
Lemma lem8217326 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) : (term557 P a i b a') = (term582 P a i b a').
Proof. exact (MK_COMB (@lem8217325 P a a' i) (@lem8217299 P i b a')). Qed.
Lemma lem8217327 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term582 P a i b a'.
Proof. exact (EQ_MP (@lem8217326 P a i b a') (@lem8217180 P a i b a' h1)). Qed.
Lemma lem8217328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217329 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8217338 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217339 {B C P : Type'} (f : type555 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> nat) f x).
Proof. exact (@lem8217338 (B -> C) (type1425 P) f x). Qed.
Lemma lem8217340 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (h f) = (@I ((B -> C) -> P -> nat -> nat) h f).
Proof. exact (@lem8217339 B C P h f). Qed.
Lemma lem8217341 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8217342 {B C P : Type'} (h : type555 B C P) (f : B -> C) (a' : P) : (h f a') = (@I ((B -> C) -> P -> nat -> nat) h f a').
Proof. exact (MK_COMB (@lem8217340 B C P h f) (@lem8217341 P a')). Qed.
Lemma lem8217344 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217345 {P : Type'} (f : type1425 P) (x : P) : (f x) = (@I (P -> nat -> nat) f x).
Proof. exact (@lem8217344 P (nat -> nat) f x). Qed.
Lemma lem8217346 {B C P : Type'} (h : type555 B C P) (f : B -> C) (a' : P) : (@I ((B -> C) -> P -> nat -> nat) h f a') = (term583 B C P h f a').
Proof. exact (@lem8217345 P (@I ((B -> C) -> P -> nat -> nat) h f) a'). Qed.
Lemma lem8217347 {B C P : Type'} (h : type555 B C P) (f : B -> C) (a' : P) : (h f a') = (term583 B C P h f a').
Proof. exact (TRANS (@lem8217342 B C P h f a') (@lem8217346 B C P h f a')). Qed.
Lemma lem8217348 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8217349 {B C P : Type'} (h : type555 B C P) (f : B -> C) (a' : P) (i : nat) : (h f a' i) = (term584 B C P h f a' i).
Proof. exact (MK_COMB (@lem8217347 B C P h f a') (@lem8217348 i)). Qed.
Lemma lem8217351 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217352 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem8217351 nat nat f x). Qed.
Lemma lem8217353 {B C P : Type'} (h : type555 B C P) (f : B -> C) (a' : P) (i : nat) : (term584 B C P h f a' i) = (term585 B C P h f a' i).
Proof. exact (@lem8217352 (term583 B C P h f a') i). Qed.
Lemma lem8217355 {B C P : Type'} (h : type555 B C P) (f : B -> C) (a' : P) (i : nat) : (h f a' i) = (term585 B C P h f a' i).
Proof. exact (TRANS (@lem8217349 B C P h f a' i) (@lem8217353 B C P h f a' i)). Qed.
Lemma lem8217364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217365 {B C P : Type'} (f : type555 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> nat) f x).
Proof. exact (@lem8217364 (B -> C) (type1425 P) f x). Qed.
Lemma lem8217366 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (h g) = (@I ((B -> C) -> P -> nat -> nat) h g).
Proof. exact (@lem8217365 B C P h g). Qed.
Lemma lem8217367 {P : Type'} (a' : P) : a' = a'.
Proof. exact (eq_refl a'). Qed.
Lemma lem8217368 {B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (h g a') = (@I ((B -> C) -> P -> nat -> nat) h g a').
Proof. exact (MK_COMB (@lem8217366 B C P h g) (@lem8217367 P a')). Qed.
Lemma lem8217370 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217371 {P : Type'} (f : type1425 P) (x : P) : (f x) = (@I (P -> nat -> nat) f x).
Proof. exact (@lem8217370 P (nat -> nat) f x). Qed.
Lemma lem8217372 {B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (@I ((B -> C) -> P -> nat -> nat) h g a') = (term583 B C P h g a').
Proof. exact (@lem8217371 P (@I ((B -> C) -> P -> nat -> nat) h g) a'). Qed.
Lemma lem8217373 {B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (h g a') = (term583 B C P h g a').
Proof. exact (TRANS (@lem8217368 B C P h g a') (@lem8217372 B C P h g a')). Qed.
Lemma lem8217374 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem8217375 {B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (h g a' i) = (term584 B C P h g a' i).
Proof. exact (MK_COMB (@lem8217373 B C P h g a') (@lem8217374 i)). Qed.
Lemma lem8217377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217378 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem8217377 nat nat f x). Qed.
Lemma lem8217379 {B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (term584 B C P h g a' i) = (term585 B C P h g a' i).
Proof. exact (@lem8217378 (term583 B C P h g a') i). Qed.
Lemma lem8217381 {B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (h g a' i) = (term585 B C P h g a' i).
Proof. exact (TRANS (@lem8217375 B C P h g a' i) (@lem8217379 B C P h g a' i)). Qed.
Lemma lem8217382 {B C P : Type'} (h : type555 B C P) (f : B -> C) (a' : P) (i : nat) : (term201 B C P h f a' i) = (term586 B C P h f a' i).
Proof. exact (MK_COMB (@lem8217329) (@lem8217355 B C P h f a' i)). Qed.
Lemma lem8217383 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : ((h f a' i) = (h g a' i)) = ((term585 B C P h f a' i) = (term585 B C P h g a' i)).
Proof. exact (MK_COMB (@lem8217382 B C P h f a' i) (@lem8217381 B C P h g a' i)). Qed.
Lemma lem8217384 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (term365 B C P f h g a' i) = (term587 B C P f h g a' i).
Proof. exact (MK_COMB (@lem8217328) (@lem8217383 B C P f h g a' i)). Qed.
Lemma lem8217386 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem8217395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217396 {B C P : Type'} (f : type555 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> nat) f x).
Proof. exact (@lem8217395 (B -> C) (type1425 P) f x). Qed.
Lemma lem8217397 {B C P : Type'} (h : type555 B C P) (f : B -> C) : (h f) = (@I ((B -> C) -> P -> nat -> nat) h f).
Proof. exact (@lem8217396 B C P h f). Qed.
Lemma lem8217398 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8217399 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) : (h f p2) = (@I ((B -> C) -> P -> nat -> nat) h f p2).
Proof. exact (MK_COMB (@lem8217397 B C P h f) (@lem8217398 P p2)). Qed.
Lemma lem8217401 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217402 {P : Type'} (f : type1425 P) (x : P) : (f x) = (@I (P -> nat -> nat) f x).
Proof. exact (@lem8217401 P (nat -> nat) f x). Qed.
Lemma lem8217403 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) : (@I ((B -> C) -> P -> nat -> nat) h f p2) = (term583 B C P h f p2).
Proof. exact (@lem8217402 P (@I ((B -> C) -> P -> nat -> nat) h f) p2). Qed.
Lemma lem8217404 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) : (h f p2) = (term583 B C P h f p2).
Proof. exact (TRANS (@lem8217399 B C P h f p2) (@lem8217403 B C P h f p2)). Qed.
Lemma lem8217405 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217406 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (h f p2 p1) = (term584 B C P h f p2 p1).
Proof. exact (MK_COMB (@lem8217404 B C P h f p2) (@lem8217405 p1)). Qed.
Lemma lem8217408 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217409 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem8217408 nat nat f x). Qed.
Lemma lem8217410 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term584 B C P h f p2 p1) = (term585 B C P h f p2 p1).
Proof. exact (@lem8217409 (term583 B C P h f p2) p1). Qed.
Lemma lem8217412 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (h f p2 p1) = (term585 B C P h f p2 p1).
Proof. exact (TRANS (@lem8217406 B C P h f p2 p1) (@lem8217410 B C P h f p2 p1)). Qed.
Lemma lem8217421 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217422 {B C P : Type'} (f : type555 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> nat -> nat) f x).
Proof. exact (@lem8217421 (B -> C) (type1425 P) f x). Qed.
Lemma lem8217423 {B C P : Type'} (h : type555 B C P) (g : B -> C) : (h g) = (@I ((B -> C) -> P -> nat -> nat) h g).
Proof. exact (@lem8217422 B C P h g). Qed.
Lemma lem8217424 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8217425 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) : (h g p2) = (@I ((B -> C) -> P -> nat -> nat) h g p2).
Proof. exact (MK_COMB (@lem8217423 B C P h g) (@lem8217424 P p2)). Qed.
Lemma lem8217427 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217428 {P : Type'} (f : type1425 P) (x : P) : (f x) = (@I (P -> nat -> nat) f x).
Proof. exact (@lem8217427 P (nat -> nat) f x). Qed.
Lemma lem8217429 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) : (@I ((B -> C) -> P -> nat -> nat) h g p2) = (term583 B C P h g p2).
Proof. exact (@lem8217428 P (@I ((B -> C) -> P -> nat -> nat) h g) p2). Qed.
Lemma lem8217430 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) : (h g p2) = (term583 B C P h g p2).
Proof. exact (TRANS (@lem8217425 B C P h g p2) (@lem8217429 B C P h g p2)). Qed.
Lemma lem8217431 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217432 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (h g p2 p1) = (term584 B C P h g p2 p1).
Proof. exact (MK_COMB (@lem8217430 B C P h g p2) (@lem8217431 p1)). Qed.
Lemma lem8217434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217435 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem8217434 nat nat f x). Qed.
Lemma lem8217436 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term584 B C P h g p2 p1) = (term585 B C P h g p2 p1).
Proof. exact (@lem8217435 (term583 B C P h g p2) p1). Qed.
Lemma lem8217438 {B C P : Type'} (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (h g p2 p1) = (term585 B C P h g p2 p1).
Proof. exact (TRANS (@lem8217432 B C P h g p2 p1) (@lem8217436 B C P h g p2 p1)). Qed.
Lemma lem8217439 {B C P : Type'} (h : type555 B C P) (f : B -> C) (p2 : P) (p1 : nat) : (term201 B C P h f p2 p1) = (term586 B C P h f p2 p1).
Proof. exact (MK_COMB (@lem8217386) (@lem8217412 B C P h f p2 p1)). Qed.
Lemma lem8217440 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((h f p2 p1) = (h g p2 p1)) = ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1)).
Proof. exact (MK_COMB (@lem8217439 B C P h f p2 p1) (@lem8217438 B C P h g p2 p1)). Qed.
Lemma lem8217441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217442 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem8217443 {B C : Type'} (f : B -> C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8217454 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217455 {B C P : Type'} (f : type521 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8217454 (B -> C) (type567 B C P) f x). Qed.
Lemma lem8217456 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f).
Proof. exact (@lem8217455 B C P z f). Qed.
Lemma lem8217457 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8217458 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g).
Proof. exact (MK_COMB (@lem8217456 B C P z f) (@lem8217457 B C g)). Qed.
Lemma lem8217460 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217461 {B C P : Type'} (f : type567 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8217460 (B -> C) (type1599 B P) f x). Qed.
Lemma lem8217462 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g) = (term588 B C P z f g).
Proof. exact (@lem8217461 B C P (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f) g). Qed.
Lemma lem8217463 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (term588 B C P z f g).
Proof. exact (TRANS (@lem8217458 B C P z f g) (@lem8217462 B C P z f g)). Qed.
Lemma lem8217464 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217465 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term589 B C P z f g p1).
Proof. exact (MK_COMB (@lem8217463 B C P z f g) (@lem8217464 p1)). Qed.
Lemma lem8217467 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217468 {B P : Type'} (f : type1599 B P) (x : nat) : (f x) = (@I (nat -> P -> B) f x).
Proof. exact (@lem8217467 nat (P -> B) f x). Qed.
Lemma lem8217469 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (term589 B C P z f g p1) = (term590 B C P z f g p1).
Proof. exact (@lem8217468 B P (term588 B C P z f g) p1). Qed.
Lemma lem8217470 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term590 B C P z f g p1).
Proof. exact (TRANS (@lem8217465 B C P z f g p1) (@lem8217469 B C P z f g p1)). Qed.
Lemma lem8217471 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8217472 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term591 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8217470 B C P z f g p1) (@lem8217471 P p2)). Qed.
Lemma lem8217474 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217475 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8217474 P B f x). Qed.
Lemma lem8217476 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term591 B C P z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (@lem8217475 B P (term590 B C P z f g p1) p2). Qed.
Lemma lem8217478 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8217472 B C P z f g p1 p2) (@lem8217476 B C P z f g p1 p2)). Qed.
Lemma lem8217479 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term593 B C P z f g p1 p2) = (term594 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8217443 B C f) (@lem8217478 B C P z f g p1 p2)). Qed.
Lemma lem8217481 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217482 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8217481 B C f x). Qed.
Lemma lem8217483 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term594 B C P z f g p1 p2) = (term595 B C P z f g p1 p2).
Proof. exact (@lem8217482 B C f (term592 B C P z f g p1 p2)). Qed.
Lemma lem8217484 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term593 B C P z f g p1 p2) = (term595 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8217479 B C P z f g p1 p2) (@lem8217483 B C P z f g p1 p2)). Qed.
Lemma lem8217485 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8217496 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217497 {B C P : Type'} (f : type521 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8217496 (B -> C) (type567 B C P) f x). Qed.
Lemma lem8217498 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f).
Proof. exact (@lem8217497 B C P z f). Qed.
Lemma lem8217499 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8217500 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g).
Proof. exact (MK_COMB (@lem8217498 B C P z f) (@lem8217499 B C g)). Qed.
Lemma lem8217502 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217503 {B C P : Type'} (f : type567 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8217502 (B -> C) (type1599 B P) f x). Qed.
Lemma lem8217504 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g) = (term588 B C P z f g).
Proof. exact (@lem8217503 B C P (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f) g). Qed.
Lemma lem8217505 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (term588 B C P z f g).
Proof. exact (TRANS (@lem8217500 B C P z f g) (@lem8217504 B C P z f g)). Qed.
Lemma lem8217506 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217507 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term589 B C P z f g p1).
Proof. exact (MK_COMB (@lem8217505 B C P z f g) (@lem8217506 p1)). Qed.
Lemma lem8217509 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217510 {B P : Type'} (f : type1599 B P) (x : nat) : (f x) = (@I (nat -> P -> B) f x).
Proof. exact (@lem8217509 nat (P -> B) f x). Qed.
Lemma lem8217511 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (term589 B C P z f g p1) = (term590 B C P z f g p1).
Proof. exact (@lem8217510 B P (term588 B C P z f g) p1). Qed.
Lemma lem8217512 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term590 B C P z f g p1).
Proof. exact (TRANS (@lem8217507 B C P z f g p1) (@lem8217511 B C P z f g p1)). Qed.
Lemma lem8217513 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8217514 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term591 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8217512 B C P z f g p1) (@lem8217513 P p2)). Qed.
Lemma lem8217516 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217517 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8217516 P B f x). Qed.
Lemma lem8217518 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term591 B C P z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (@lem8217517 B P (term590 B C P z f g p1) p2). Qed.
Lemma lem8217520 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8217514 B C P z f g p1 p2) (@lem8217518 B C P z f g p1 p2)). Qed.
Lemma lem8217521 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term596 B C P z f g p1 p2) = (term597 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8217485 B C g) (@lem8217520 B C P z f g p1 p2)). Qed.
Lemma lem8217523 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217524 {B C : Type'} (f : B -> C) (x : B) : (f x) = (@I (B -> C) f x).
Proof. exact (@lem8217523 B C f x). Qed.
Lemma lem8217525 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term597 B C P z f g p1 p2) = (term598 B C P z f g p1 p2).
Proof. exact (@lem8217524 B C g (term592 B C P z f g p1 p2)). Qed.
Lemma lem8217526 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term596 B C P z f g p1 p2) = (term598 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8217521 B C P z f g p1 p2) (@lem8217525 B C P z f g p1 p2)). Qed.
Lemma lem8217527 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term599 B C P z f g p1 p2) = (term600 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8217442 C) (@lem8217484 B C P z f g p1 p2)). Qed.
Lemma lem8217528 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : ((term593 B C P z f g p1 p2) = (term596 B C P z f g p1 p2)) = ((term595 B C P z f g p1 p2) = (term598 B C P z f g p1 p2)).
Proof. exact (MK_COMB (@lem8217527 B C P z f g p1 p2) (@lem8217526 B C P z f g p1 p2)). Qed.
Lemma lem8217529 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term601 B C P z f g p1 p2) = (term602 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8217441) (@lem8217528 B C P z f g p1 p2)). Qed.
Lemma lem8217530 {A B : Type'} (lt2 : type1470 A B) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem8217541 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217542 {B C P : Type'} (f : type521 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8217541 (B -> C) (type567 B C P) f x). Qed.
Lemma lem8217543 {B C P : Type'} (z : type521 B C P) (f : B -> C) : (z f) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f).
Proof. exact (@lem8217542 B C P z f). Qed.
Lemma lem8217544 {B C : Type'} (g : B -> C) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8217545 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g).
Proof. exact (MK_COMB (@lem8217543 B C P z f) (@lem8217544 B C g)). Qed.
Lemma lem8217547 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217548 {B C P : Type'} (f : type567 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> nat -> P -> B) f x).
Proof. exact (@lem8217547 (B -> C) (type1599 B P) f x). Qed.
Lemma lem8217549 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f g) = (term588 B C P z f g).
Proof. exact (@lem8217548 B C P (@I ((B -> C) -> (B -> C) -> nat -> P -> B) z f) g). Qed.
Lemma lem8217550 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) : (z f g) = (term588 B C P z f g).
Proof. exact (TRANS (@lem8217545 B C P z f g) (@lem8217549 B C P z f g)). Qed.
Lemma lem8217551 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217552 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term589 B C P z f g p1).
Proof. exact (MK_COMB (@lem8217550 B C P z f g) (@lem8217551 p1)). Qed.
Lemma lem8217554 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217555 {B P : Type'} (f : type1599 B P) (x : nat) : (f x) = (@I (nat -> P -> B) f x).
Proof. exact (@lem8217554 nat (P -> B) f x). Qed.
Lemma lem8217556 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (term589 B C P z f g p1) = (term590 B C P z f g p1).
Proof. exact (@lem8217555 B P (term588 B C P z f g) p1). Qed.
Lemma lem8217557 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) : (z f g p1) = (term590 B C P z f g p1).
Proof. exact (TRANS (@lem8217552 B C P z f g p1) (@lem8217556 B C P z f g p1)). Qed.
Lemma lem8217558 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8217559 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term591 B C P z f g p1 p2).
Proof. exact (MK_COMB (@lem8217557 B C P z f g p1) (@lem8217558 P p2)). Qed.
Lemma lem8217561 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217562 {B P : Type'} (f : P -> B) (x : P) : (f x) = (@I (P -> B) f x).
Proof. exact (@lem8217561 P B f x). Qed.
Lemma lem8217563 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term591 B C P z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (@lem8217562 B P (term590 B C P z f g p1) p2). Qed.
Lemma lem8217565 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (z f g p1 p2) = (term592 B C P z f g p1 p2).
Proof. exact (TRANS (@lem8217559 B C P z f g p1 p2) (@lem8217563 B C P z f g p1 p2)). Qed.
Lemma lem8217570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217571 {A P : Type'} (f : P -> A) (x : P) : (f x) = (@I (P -> A) f x).
Proof. exact (@lem8217570 P A f x). Qed.
Lemma lem8217573 {A P : Type'} (s : P -> A) (p2 : P) : (s p2) = (@I (P -> A) s p2).
Proof. exact (@lem8217571 A P s p2). Qed.
Lemma lem8217574 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term603 A B C P lt2 z f g p1 p2) = (term604 A B C P lt2 z f g p1 p2).
Proof. exact (MK_COMB (@lem8217530 A B lt2) (@lem8217565 B C P z f g p1 p2)). Qed.
Lemma lem8217575 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term605 A B C P lt2 z f g p1 s p2) = (term606 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8217574 A B C P lt2 z f g p1 p2) (@lem8217573 A P s p2)). Qed.
Lemma lem8217577 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217578 {A B : Type'} (f : type1470 A B) (x : B) : (f x) = (@I (B -> A -> Prop) f x).
Proof. exact (@lem8217577 B (A -> Prop) f x). Qed.
Lemma lem8217579 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term604 A B C P lt2 z f g p1 p2) = (term607 A B C P lt2 z f g p1 p2).
Proof. exact (@lem8217578 A B lt2 (term592 B C P z f g p1 p2)). Qed.
Lemma lem8217580 {A P : Type'} (s : P -> A) (p2 : P) : (@I (P -> A) s p2) = (@I (P -> A) s p2).
Proof. exact (eq_refl (@I (P -> A) s p2)). Qed.
Lemma lem8217581 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term606 A B C P lt2 z f g p1 s p2) = (term608 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8217579 A B C P lt2 z f g p1 p2) (@lem8217580 A P s p2)). Qed.
Lemma lem8217583 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217584 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem8217583 A Prop f x). Qed.
Lemma lem8217585 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term608 A B C P lt2 z f g p1 s p2) = (term609 A B C P lt2 z f g p1 s p2).
Proof. exact (@lem8217584 A (term607 A B C P lt2 z f g p1 p2) (@I (P -> A) s p2)). Qed.
Lemma lem8217586 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term606 A B C P lt2 z f g p1 s p2) = (term609 A B C P lt2 z f g p1 s p2).
Proof. exact (TRANS (@lem8217581 A B C P lt2 z f g p1 s p2) (@lem8217585 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8217587 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term605 A B C P lt2 z f g p1 s p2) = (term609 A B C P lt2 z f g p1 s p2).
Proof. exact (TRANS (@lem8217575 A B C P lt2 z f g p1 s p2) (@lem8217586 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8217588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8217589 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (s : P -> A) (p2 : P) : (term610 A B C P lt2 z f g p1 s p2) = (term611 A B C P lt2 z f g p1 s p2).
Proof. exact (MK_COMB (@lem8217588) (@lem8217587 A B C P lt2 z f g p1 s p2)). Qed.
Lemma lem8217590 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term612 A B C P lt2 s z f g p1 p2) = (term613 A B C P lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8217589 A B C P lt2 z f g p1 s p2) (@lem8217529 B C P z f g p1 p2)). Qed.
Lemma lem8217591 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217598 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217599 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8217598 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8217600 {B C P : Type'} (p : type560 B C P) (g : B -> C) : (p g) = (@I ((B -> C) -> P -> Prop) p g).
Proof. exact (@lem8217599 B C P p g). Qed.
Lemma lem8217601 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8217602 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (p g p2) = (@I ((B -> C) -> P -> Prop) p g p2).
Proof. exact (MK_COMB (@lem8217600 B C P p g) (@lem8217601 P p2)). Qed.
Lemma lem8217604 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217605 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8217604 P Prop f x). Qed.
Lemma lem8217606 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (@I ((B -> C) -> P -> Prop) p g p2) = (term558 B C P p g p2).
Proof. exact (@lem8217605 P (@I ((B -> C) -> P -> Prop) p g) p2). Qed.
Lemma lem8217608 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (p g p2) = (term558 B C P p g p2).
Proof. exact (TRANS (@lem8217602 B C P p g p2) (@lem8217606 B C P p g p2)). Qed.
Lemma lem8217609 {B C P : Type'} (p : type560 B C P) (g : B -> C) (p2 : P) : (term614 B C P p g p2) = (term615 B C P p g p2).
Proof. exact (MK_COMB (@lem8217591) (@lem8217608 B C P p g p2)). Qed.
Lemma lem8217610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217618 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8217617 P nat f x). Qed.
Lemma lem8217620 {P : Type'} (b : P -> nat) (p2 : P) : (b p2) = (@I (P -> nat) b p2).
Proof. exact (@lem8217618 P b p2). Qed.
Lemma lem8217621 (p1 : nat) : (Peano.le p1) = (Peano.le p1).
Proof. exact (eq_refl (Peano.le p1)). Qed.
Lemma lem8217622 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term571 P p1 b p2).
Proof. exact (MK_COMB (@lem8217621 p1) (@lem8217620 P b p2)). Qed.
Lemma lem8217624 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217625 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8217624 nat (nat -> Prop) f x). Qed.
Lemma lem8217626 (p1 : nat) : (Peano.le p1) = (@I (nat -> nat -> Prop) Peano.le p1).
Proof. exact (@lem8217625 Peano.le p1). Qed.
Lemma lem8217627 {P : Type'} (b : P -> nat) (p2 : P) : (@I (P -> nat) b p2) = (@I (P -> nat) b p2).
Proof. exact (eq_refl (@I (P -> nat) b p2)). Qed.
Lemma lem8217628 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term572 P p1 b p2).
Proof. exact (MK_COMB (@lem8217626 p1) (@lem8217627 P b p2)). Qed.
Lemma lem8217630 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217631 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8217630 nat Prop f x). Qed.
Lemma lem8217632 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term572 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (@lem8217631 (@I (nat -> nat -> Prop) Peano.le p1) (@I (P -> nat) b p2)). Qed.
Lemma lem8217633 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8217628 P p1 b p2) (@lem8217632 P p1 b p2)). Qed.
Lemma lem8217634 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8217622 P p1 b p2) (@lem8217633 P p1 b p2)). Qed.
Lemma lem8217635 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term616 P p1 b p2) = (term617 P p1 b p2).
Proof. exact (MK_COMB (@lem8217610) (@lem8217634 P p1 b p2)). Qed.
Lemma lem8217636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217637 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term618 P p1 b p2) = (term619 P p1 b p2).
Proof. exact (MK_COMB (@lem8217636) (@lem8217635 P p1 b p2)). Qed.
Lemma lem8217638 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term367 B C P p1 b p g p2) = (term620 B C P p1 b p g p2).
Proof. exact (MK_COMB (@lem8217637 P p1 b p2) (@lem8217609 B C P p g p2)). Qed.
Lemma lem8217639 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217640 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem8217645 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217646 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8217645 P nat f x). Qed.
Lemma lem8217648 {P : Type'} (a : P -> nat) (p2 : P) : (a p2) = (@I (P -> nat) a p2).
Proof. exact (@lem8217646 P a p2). Qed.
Lemma lem8217649 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217650 {P : Type'} (a : P -> nat) (p2 : P) : (term574 P a p2) = (term575 P a p2).
Proof. exact (MK_COMB (@lem8217640) (@lem8217648 P a p2)). Qed.
Lemma lem8217651 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term576 P a p2 p1).
Proof. exact (MK_COMB (@lem8217650 P a p2) (@lem8217649 p1)). Qed.
Lemma lem8217653 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217654 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8217653 nat (nat -> Prop) f x). Qed.
Lemma lem8217655 {P : Type'} (a : P -> nat) (p2 : P) : (term575 P a p2) = (term577 P a p2).
Proof. exact (@lem8217654 Peano.le (@I (P -> nat) a p2)). Qed.
Lemma lem8217656 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217657 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term578 P a p2 p1).
Proof. exact (MK_COMB (@lem8217655 P a p2) (@lem8217656 p1)). Qed.
Lemma lem8217659 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217660 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8217659 nat Prop f x). Qed.
Lemma lem8217661 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term578 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (@lem8217660 (term577 P a p2) p1). Qed.
Lemma lem8217662 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8217657 P a p2 p1) (@lem8217661 P a p2 p1)). Qed.
Lemma lem8217663 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8217651 P a p2 p1) (@lem8217662 P a p2 p1)). Qed.
Lemma lem8217664 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term621 P a p2 p1) = (term622 P a p2 p1).
Proof. exact (MK_COMB (@lem8217639) (@lem8217663 P a p2 p1)). Qed.
Lemma lem8217665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217666 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term623 P a p2 p1).
Proof. exact (MK_COMB (@lem8217665) (@lem8217664 P a p2 p1)). Qed.
Lemma lem8217667 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term371 B C P a p1 b p g p2) = (term624 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8217666 P a p2 p1) (@lem8217638 B C P p1 b p g p2)). Qed.
Lemma lem8217668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217669 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (p2 : P) : (term387 B C P a p1 b p g p2) = (term625 B C P a p1 b p g p2).
Proof. exact (MK_COMB (@lem8217668) (@lem8217667 B C P a p1 b p g p2)). Qed.
Lemma lem8217670 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term626 A B C P a b p lt2 s z f g p1 p2) = (term627 A B C P a b p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8217669 B C P a p1 b p g p2) (@lem8217590 A B C P lt2 s z f g p1 p2)). Qed.
Lemma lem8217671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217679 {B C P : Type'} (f : type560 B C P) (x : B -> C) : (f x) = (@I ((B -> C) -> P -> Prop) f x).
Proof. exact (@lem8217678 (B -> C) (P -> Prop) f x). Qed.
Lemma lem8217680 {B C P : Type'} (p : type560 B C P) (f : B -> C) : (p f) = (@I ((B -> C) -> P -> Prop) p f).
Proof. exact (@lem8217679 B C P p f). Qed.
Lemma lem8217681 {P : Type'} (p2 : P) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem8217682 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (p f p2) = (@I ((B -> C) -> P -> Prop) p f p2).
Proof. exact (MK_COMB (@lem8217680 B C P p f) (@lem8217681 P p2)). Qed.
Lemma lem8217684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217685 {P : Type'} (f : P -> Prop) (x : P) : (f x) = (@I (P -> Prop) f x).
Proof. exact (@lem8217684 P Prop f x). Qed.
Lemma lem8217686 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (@I ((B -> C) -> P -> Prop) p f p2) = (term558 B C P p f p2).
Proof. exact (@lem8217685 P (@I ((B -> C) -> P -> Prop) p f) p2). Qed.
Lemma lem8217688 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (p f p2) = (term558 B C P p f p2).
Proof. exact (TRANS (@lem8217682 B C P p f p2) (@lem8217686 B C P p f p2)). Qed.
Lemma lem8217689 {B C P : Type'} (p : type560 B C P) (f : B -> C) (p2 : P) : (term614 B C P p f p2) = (term615 B C P p f p2).
Proof. exact (MK_COMB (@lem8217671) (@lem8217688 B C P p f p2)). Qed.
Lemma lem8217690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217697 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217698 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8217697 P nat f x). Qed.
Lemma lem8217700 {P : Type'} (b : P -> nat) (p2 : P) : (b p2) = (@I (P -> nat) b p2).
Proof. exact (@lem8217698 P b p2). Qed.
Lemma lem8217701 (p1 : nat) : (Peano.le p1) = (Peano.le p1).
Proof. exact (eq_refl (Peano.le p1)). Qed.
Lemma lem8217702 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term571 P p1 b p2).
Proof. exact (MK_COMB (@lem8217701 p1) (@lem8217700 P b p2)). Qed.
Lemma lem8217704 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217705 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8217704 nat (nat -> Prop) f x). Qed.
Lemma lem8217706 (p1 : nat) : (Peano.le p1) = (@I (nat -> nat -> Prop) Peano.le p1).
Proof. exact (@lem8217705 Peano.le p1). Qed.
Lemma lem8217707 {P : Type'} (b : P -> nat) (p2 : P) : (@I (P -> nat) b p2) = (@I (P -> nat) b p2).
Proof. exact (eq_refl (@I (P -> nat) b p2)). Qed.
Lemma lem8217708 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term572 P p1 b p2).
Proof. exact (MK_COMB (@lem8217706 p1) (@lem8217707 P b p2)). Qed.
Lemma lem8217710 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217711 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8217710 nat Prop f x). Qed.
Lemma lem8217712 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term572 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (@lem8217711 (@I (nat -> nat -> Prop) Peano.le p1) (@I (P -> nat) b p2)). Qed.
Lemma lem8217713 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term571 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8217708 P p1 b p2) (@lem8217712 P p1 b p2)). Qed.
Lemma lem8217714 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term368 P p1 b p2) = (term573 P p1 b p2).
Proof. exact (TRANS (@lem8217702 P p1 b p2) (@lem8217713 P p1 b p2)). Qed.
Lemma lem8217715 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term616 P p1 b p2) = (term617 P p1 b p2).
Proof. exact (MK_COMB (@lem8217690) (@lem8217714 P p1 b p2)). Qed.
Lemma lem8217716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217717 {P : Type'} (p1 : nat) (b : P -> nat) (p2 : P) : (term618 P p1 b p2) = (term619 P p1 b p2).
Proof. exact (MK_COMB (@lem8217716) (@lem8217715 P p1 b p2)). Qed.
Lemma lem8217718 {B C P : Type'} (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term367 B C P p1 b p f p2) = (term620 B C P p1 b p f p2).
Proof. exact (MK_COMB (@lem8217717 P p1 b p2) (@lem8217689 B C P p f p2)). Qed.
Lemma lem8217719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8217720 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem8217725 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217726 {P : Type'} (f : P -> nat) (x : P) : (f x) = (@I (P -> nat) f x).
Proof. exact (@lem8217725 P nat f x). Qed.
Lemma lem8217728 {P : Type'} (a : P -> nat) (p2 : P) : (a p2) = (@I (P -> nat) a p2).
Proof. exact (@lem8217726 P a p2). Qed.
Lemma lem8217729 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217730 {P : Type'} (a : P -> nat) (p2 : P) : (term574 P a p2) = (term575 P a p2).
Proof. exact (MK_COMB (@lem8217720) (@lem8217728 P a p2)). Qed.
Lemma lem8217731 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term576 P a p2 p1).
Proof. exact (MK_COMB (@lem8217730 P a p2) (@lem8217729 p1)). Qed.
Lemma lem8217733 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217734 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem8217733 nat (nat -> Prop) f x). Qed.
Lemma lem8217735 {P : Type'} (a : P -> nat) (p2 : P) : (term575 P a p2) = (term577 P a p2).
Proof. exact (@lem8217734 Peano.le (@I (P -> nat) a p2)). Qed.
Lemma lem8217736 (p1 : nat) : p1 = p1.
Proof. exact (eq_refl p1). Qed.
Lemma lem8217737 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term578 P a p2 p1).
Proof. exact (MK_COMB (@lem8217735 P a p2) (@lem8217736 p1)). Qed.
Lemma lem8217739 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8217740 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem8217739 nat Prop f x). Qed.
Lemma lem8217741 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term578 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (@lem8217740 (term577 P a p2) p1). Qed.
Lemma lem8217742 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term576 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8217737 P a p2 p1) (@lem8217741 P a p2 p1)). Qed.
Lemma lem8217743 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term373 P a p2 p1) = (term579 P a p2 p1).
Proof. exact (TRANS (@lem8217731 P a p2 p1) (@lem8217742 P a p2 p1)). Qed.
Lemma lem8217744 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term621 P a p2 p1) = (term622 P a p2 p1).
Proof. exact (MK_COMB (@lem8217719) (@lem8217743 P a p2 p1)). Qed.
Lemma lem8217745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217746 {P : Type'} (a : P -> nat) (p2 : P) (p1 : nat) : (term369 P a p2 p1) = (term623 P a p2 p1).
Proof. exact (MK_COMB (@lem8217745) (@lem8217744 P a p2 p1)). Qed.
Lemma lem8217747 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term371 B C P a p1 b p f p2) = (term624 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8217746 P a p2 p1) (@lem8217718 B C P p1 b p f p2)). Qed.
Lemma lem8217748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217749 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term387 B C P a p1 b p f p2) = (term625 B C P a p1 b p f p2).
Proof. exact (MK_COMB (@lem8217748) (@lem8217747 B C P a p1 b p f p2)). Qed.
Lemma lem8217750 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term628 A B C P a b p lt2 s z f g p1 p2) = (term629 A B C P a b p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8217749 B C P a p1 b p f p2) (@lem8217670 A B C P a b p lt2 s z f g p1 p2)). Qed.
Lemma lem8217751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217752 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term630 A B C P a b p lt2 s z f g p1 p2) = (term631 A B C P a b p lt2 s z f g p1 p2).
Proof. exact (MK_COMB (@lem8217751) (@lem8217750 A B C P a b p lt2 s z f g p1 p2)). Qed.
Lemma lem8217753 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term632 A B C P a b p lt2 s z f h g p2 p1) = (term633 A B C P a b p lt2 s z f h g p2 p1).
Proof. exact (MK_COMB (@lem8217752 A B C P a b p lt2 s z f g p1 p2) (@lem8217440 B C P f h g p2 p1)). Qed.
Lemma lem8217754 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term634 A B C P a b p lt2 s z f h g p1) = (term635 A B C P a b p lt2 s z f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8217753 A B C P a b p lt2 s z f h g p2 p1)). Qed.
Lemma lem8217755 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8217756 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term636 A B C P a b p lt2 s z f h g p1) = (term637 A B C P a b p lt2 s z f h g p1).
Proof. exact (MK_COMB (@lem8217755 P) (@lem8217754 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8217757 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term638 A B C P a b p lt2 s z f h g) = (term639 A B C P a b p lt2 s z f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8217756 A B C P a b p lt2 s z f h g p1)). Qed.
Lemma lem8217758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8217759 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term640 A B C P a b p lt2 s z f h g) = (term641 A B C P a b p lt2 s z f h g).
Proof. exact (MK_COMB (@lem8217758) (@lem8217757 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217760 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) : (term642 A B C P a b p lt2 s z f h) = (term643 A B C P a b p lt2 s z f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8217759 A B C P a b p lt2 s z f h g)). Qed.
Lemma lem8217761 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217762 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (f : B -> C) (h : type555 B C P) : (term546 A B C P a b p lt2 s z f h) = (term644 A B C P a b p lt2 s z f h).
Proof. exact (MK_COMB (@lem8217761 B C) (@lem8217760 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217763 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) : (term548 A B C P a b p lt2 s z h) = (term645 A B C P a b p lt2 s z h).
Proof. exact (fun_ext (fun f : B -> C => @lem8217762 A B C P a b p lt2 s z f h)). Qed.
Lemma lem8217764 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217765 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) : (term550 A B C P a b p lt2 s z h) = (term646 A B C P a b p lt2 s z h).
Proof. exact (MK_COMB (@lem8217764 B C) (@lem8217763 A B C P a b p lt2 s z h)). Qed.
Lemma lem8217766 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term646 A B C P a b p lt2 s z h.
Proof. exact (EQ_MP (@lem8217765 A B C P a b p lt2 s z h) (@lem8217187 A B C P a b p lt2 s z h h1)). Qed.
Lemma lem8217784 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (z : B) : (term568 A B C P lt2 s a' f g z) = (term568 A B C P lt2 s a' f g z).
Proof. exact (eq_refl (term568 A B C P lt2 s a' f g z)). Qed.
Lemma lem8217785 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term569 A B C P lt2 s a' f g) = (term569 A B C P lt2 s a' f g).
Proof. exact (fun_ext (fun z : B => @lem8217784 A B C P lt2 s a' f g z)). Qed.
Lemma lem8217786 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem8217788 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) : (term570 A B C P lt2 s a' f g) = (term570 A B C P lt2 s a' f g).
Proof. exact (MK_COMB (@lem8217786 B) (@lem8217785 A B C P lt2 s a' f g)). Qed.
Lemma lem8217789 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term570 A B C P lt2 s a' f g.
Proof. exact (EQ_MP (@lem8217788 A B C P lt2 s a' f g) (@lem8217275 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8217795 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1)) = ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1)).
Proof. exact (eq_refl ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1))). Qed.
Lemma lem8217824 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term627 A B C P a b p lt2 s z f g p1 p2) = (term647 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (@lem19490 (term609 A B C P lt2 z f g p1 s p2) (term624 B C P a p1 b p g p2) (term602 B C P z f g p1 p2)). Qed.
Lemma lem8217839 {B C P : Type'} (a : P -> nat) (p1 : nat) (b : P -> nat) (p : type560 B C P) (f : B -> C) (p2 : P) : (term625 B C P a p1 b p f p2) = (term625 B C P a p1 b p f p2).
Proof. exact (eq_refl (term625 B C P a p1 b p f p2)). Qed.
Lemma lem8217840 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term629 A B C P a b p lt2 s z f g p1 p2) = (term648 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (MK_COMB (@lem8217839 B C P a p1 b p f p2) (@lem8217824 A B C P lt2 s a b p z f g p1 p2)). Qed.
Lemma lem8217847 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term648 A B C P lt2 s a b p z f g p1 p2) = (term649 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (@lem19490 (term650 A B C P a b p lt2 z f g p1 s p2) (term624 B C P a p1 b p f p2) (term651 B C P a b p z f g p1 p2)). Qed.
Lemma lem8217848 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term629 A B C P a b p lt2 s z f g p1 p2) = (term649 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (TRANS (@lem8217840 A B C P lt2 s a b p z f g p1 p2) (@lem8217847 A B C P lt2 s a b p z f g p1 p2)). Qed.
Lemma lem8217849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8217850 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (g : B -> C) (p1 : nat) (p2 : P) : (term631 A B C P a b p lt2 s z f g p1 p2) = (term652 A B C P lt2 s a b p z f g p1 p2).
Proof. exact (MK_COMB (@lem8217849) (@lem8217848 A B C P lt2 s a b p z f g p1 p2)). Qed.
Lemma lem8217851 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term633 A B C P a b p lt2 s z f h g p2 p1) = (term653 A B C P lt2 s a b p z f h g p2 p1).
Proof. exact (MK_COMB (@lem8217850 A B C P lt2 s a b p z f g p1 p2) (@lem8217795 B C P f h g p2 p1)). Qed.
Lemma lem8217858 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term653 A B C P lt2 s a b p z f h g p2 p1) = (term654 A B C P lt2 s a b p z f h g p2 p1).
Proof. exact (@lem19699 (term655 A B C P a b p lt2 z f g p1 s p2) (term656 B C P a b p z f g p1 p2) ((term585 B C P h f p2 p1) = (term585 B C P h g p2 p1))). Qed.
Lemma lem8217859 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p2 : P) (p1 : nat) : (term633 A B C P a b p lt2 s z f h g p2 p1) = (term654 A B C P lt2 s a b p z f h g p2 p1).
Proof. exact (TRANS (@lem8217851 A B C P lt2 s a b p z f h g p2 p1) (@lem8217858 A B C P lt2 s a b p z f h g p2 p1)). Qed.
Lemma lem8217860 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term635 A B C P a b p lt2 s z f h g p1) = (term657 A B C P lt2 s a b p z f h g p1).
Proof. exact (fun_ext (fun p2 : P => @lem8217859 A B C P lt2 s a b p z f h g p2 p1)). Qed.
Lemma lem8217861 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8217862 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) (p1 : nat) : (term637 A B C P a b p lt2 s z f h g p1) = (term658 A B C P lt2 s a b p z f h g p1).
Proof. exact (MK_COMB (@lem8217861 P) (@lem8217860 A B C P lt2 s a b p z f h g p1)). Qed.
Lemma lem8217863 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term639 A B C P a b p lt2 s z f h g) = (term659 A B C P lt2 s a b p z f h g).
Proof. exact (fun_ext (fun p1 : nat => @lem8217862 A B C P lt2 s a b p z f h g p1)). Qed.
Lemma lem8217864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem8217865 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) (g : B -> C) : (term641 A B C P a b p lt2 s z f h g) = (term660 A B C P lt2 s a b p z f h g).
Proof. exact (MK_COMB (@lem8217864) (@lem8217863 A B C P lt2 s a b p z f h g)). Qed.
Lemma lem8217866 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) : (term643 A B C P a b p lt2 s z f h) = (term661 A B C P lt2 s a b p z f h).
Proof. exact (fun_ext (fun g : B -> C => @lem8217865 A B C P lt2 s a b p z f h g)). Qed.
Lemma lem8217867 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217868 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (f : B -> C) (h : type555 B C P) : (term644 A B C P a b p lt2 s z f h) = (term662 A B C P lt2 s a b p z f h).
Proof. exact (MK_COMB (@lem8217867 B C) (@lem8217866 A B C P lt2 s a b p z f h)). Qed.
Lemma lem8217869 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (h : type555 B C P) : (term645 A B C P a b p lt2 s z h) = (term663 A B C P lt2 s a b p z h).
Proof. exact (fun_ext (fun f : B -> C => @lem8217868 A B C P lt2 s a b p z f h)). Qed.
Lemma lem8217870 {B C : Type'} : (@all (B -> C)) = (@all (B -> C)).
Proof. exact (eq_refl (@all (B -> C))). Qed.
Lemma lem8217872 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (h : type555 B C P) : (term646 A B C P a b p lt2 s z h) = (term664 A B C P lt2 s a b p z h).
Proof. exact (MK_COMB (@lem8217870 B C) (@lem8217869 A B C P lt2 s a b p z h)). Qed.
Lemma lem8217873 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term664 A B C P lt2 s a b p z h.
Proof. exact (EQ_MP (@lem8217872 A B C P lt2 s a b p z h) (@lem8217766 A B C P a b p lt2 s z h h1)). Qed.
Lemma lem8217882 {A B C P : Type'} (_109197 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term665 A B C P lt2 s a' f g _109197.
Proof. exact (@lem8217789 A B C P lt2 s a' f g h1 _109197). Qed.
Lemma lem8217883 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109197 : B) : (term665 A B C P lt2 s a' f g _109197) = (term568 A B C P lt2 s a' f g _109197).
Proof. exact (eq_refl (term665 A B C P lt2 s a' f g _109197)). Qed.
Lemma lem8217885 {A B C P : Type'} (_109198 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term666 A B C P lt2 s a b p z h _109198.
Proof. exact (@lem8217873 A B C P a b p lt2 s z h h1 _109198). Qed.
Lemma lem8217886 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) : (term666 A B C P lt2 s a b p z h _109198) = (term662 A B C P lt2 s a b p z _109198 h).
Proof. exact (eq_refl (term666 A B C P lt2 s a b p z h _109198)). Qed.
Lemma lem8217887 {A B C P : Type'} (_109198 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term662 A B C P lt2 s a b p z _109198 h.
Proof. exact (EQ_MP (@lem8217886 A B C P lt2 s a b p z _109198 h) (@lem8217885 A B C P _109198 a b p lt2 s z h h1)). Qed.
Lemma lem8217888 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term667 A B C P lt2 s a b p z _109198 h _109199.
Proof. exact (@lem8217887 A B C P _109198 a b p lt2 s z h h1 _109199). Qed.
Lemma lem8217889 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) : (term667 A B C P lt2 s a b p z _109198 h _109199) = (term660 A B C P lt2 s a b p z _109198 h _109199).
Proof. exact (eq_refl (term667 A B C P lt2 s a b p z _109198 h _109199)). Qed.
Lemma lem8217890 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term660 A B C P lt2 s a b p z _109198 h _109199.
Proof. exact (EQ_MP (@lem8217889 A B C P lt2 s a b p z _109198 h _109199) (@lem8217888 A B C P _109198 _109199 a b p lt2 s z h h1)). Qed.
Lemma lem8217891 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term668 A B C P lt2 s a b p z _109198 h _109199 _109200.
Proof. exact (@lem8217890 A B C P _109198 _109199 a b p lt2 s z h h1 _109200). Qed.
Lemma lem8217892 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109200 : nat) : (term668 A B C P lt2 s a b p z _109198 h _109199 _109200) = (term658 A B C P lt2 s a b p z _109198 h _109199 _109200).
Proof. exact (eq_refl (term668 A B C P lt2 s a b p z _109198 h _109199 _109200)). Qed.
Lemma lem8217893 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term658 A B C P lt2 s a b p z _109198 h _109199 _109200.
Proof. exact (EQ_MP (@lem8217892 A B C P lt2 s a b p z _109198 h _109199 _109200) (@lem8217891 A B C P _109198 _109199 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8217894 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term669 A B C P lt2 s a b p z _109198 h _109199 _109200 _109201.
Proof. exact (@lem8217893 A B C P _109198 _109199 _109200 a b p lt2 s z h h1 _109201). Qed.
Lemma lem8217895 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term669 A B C P lt2 s a b p z _109198 h _109199 _109200 _109201) = (term654 A B C P lt2 s a b p z _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term669 A B C P lt2 s a b p z _109198 h _109199 _109200 _109201)). Qed.
Lemma lem8217896 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term654 A B C P lt2 s a b p z _109198 h _109199 _109201 _109200.
Proof. exact (EQ_MP (@lem8217895 A B C P lt2 s a b p z _109198 h _109199 _109201 _109200) (@lem8217894 A B C P _109198 _109199 _109200 _109201 a b p lt2 s z h h1)). Qed.
Lemma lem8217897 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term670 B C P a b p z _109198 h _109199 _109201 _109200.
Proof. exact (proj2 (@lem8217896 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8217898 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term671 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200.
Proof. exact (proj1 (@lem8217896 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8217908 {A B C P : Type'} (_109197 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term568 A B C P lt2 s a' f g _109197.
Proof. exact (EQ_MP (@lem8217883 A B C P lt2 s a' f g _109197) (@lem8217882 A B C P _109197 lt2 s a' f g h1)). Qed.
Lemma lem8217910 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term587 B C P f h g a' i.
Proof. exact (EQ_MP (@lem8217384 B C P f h g a' i) (@lem8217186 B C P f h g a' i h1)). Qed.
Lemma lem8217918 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term671 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term672 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term624 B C P a _109200 b p _109198 _109201) (term650 A B C P a b p lt2 z _109198 _109199 _109200 s _109201) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8217919 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term673 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term674 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term624 B C P a _109200 b p _109199 _109201) (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8217923 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term674 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term675 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term622 P a _109201 _109200) (term620 B C P _109200 b p _109199 _109201) (term676 A B C P lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217930 {A B C P : Type'} (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term677 A B C P b p lt2 z s _109198 h _109199 _109201 _109200) = (term678 A B C P b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term617 P _109200 b _109201) (term615 B C P p _109199 _109201) (term676 A B C P lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217931 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term623 P a _109201 _109200) = (term623 P a _109201 _109200).
Proof. exact (eq_refl (term623 P a _109201 _109200)). Qed.
Lemma lem8217934 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term675 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8217931 P a _109201 _109200) (@lem8217930 A B C P b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217936 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term674 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217923 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8217934 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217937 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term673 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217919 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8217936 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217938 {B C P : Type'} (a : P -> nat) (_109200 : nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term625 B C P a _109200 b p _109198 _109201) = (term625 B C P a _109200 b p _109198 _109201).
Proof. exact (eq_refl (term625 B C P a _109200 b p _109198 _109201)). Qed.
Lemma lem8217939 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term672 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term680 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8217938 B C P a _109200 b p _109198 _109201) (@lem8217937 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217940 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term680 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term681 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term622 P a _109201 _109200) (term620 B C P _109200 b p _109198 _109201) (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217947 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term682 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term683 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term617 P _109200 b _109201) (term615 B C P p _109198 _109201) (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217948 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term623 P a _109201 _109200) = (term623 P a _109201 _109200).
Proof. exact (eq_refl (term623 P a _109201 _109200)). Qed.
Lemma lem8217951 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term681 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8217948 P a _109201 _109200) (@lem8217947 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217952 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term680 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217940 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8217951 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217953 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term672 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217939 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8217952 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217955 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term671 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217918 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8217953 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217956 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200.
Proof. exact (EQ_MP (@lem8217955 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8217898 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8217960 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term670 B C P a b p z _109198 h _109199 _109201 _109200) = (term685 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term624 B C P a _109200 b p _109198 _109201) (term651 B C P a b p z _109198 _109199 _109200 _109201) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8217961 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term686 B C P a b p z _109198 h _109199 _109201 _109200) = (term687 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term624 B C P a _109200 b p _109199 _109201) (term602 B C P z _109198 _109199 _109200 _109201) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8217965 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term687 B C P a b p z _109198 h _109199 _109201 _109200) = (term688 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term622 P a _109201 _109200) (term620 B C P _109200 b p _109199 _109201) (term689 B C P z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217972 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term690 B C P b p z _109198 h _109199 _109201 _109200) = (term691 B C P b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term617 P _109200 b _109201) (term615 B C P p _109199 _109201) (term689 B C P z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217973 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term623 P a _109201 _109200) = (term623 P a _109201 _109200).
Proof. exact (eq_refl (term623 P a _109201 _109200)). Qed.
Lemma lem8217976 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term688 B C P a b p z _109198 h _109199 _109201 _109200) = (term692 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8217973 P a _109201 _109200) (@lem8217972 B C P b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217978 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term687 B C P a b p z _109198 h _109199 _109201 _109200) = (term692 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217965 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8217976 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217979 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term686 B C P a b p z _109198 h _109199 _109201 _109200) = (term692 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217961 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8217978 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217980 {B C P : Type'} (a : P -> nat) (_109200 : nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term625 B C P a _109200 b p _109198 _109201) = (term625 B C P a _109200 b p _109198 _109201).
Proof. exact (eq_refl (term625 B C P a _109200 b p _109198 _109201)). Qed.
Lemma lem8217981 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term685 B C P a b p z _109198 h _109199 _109201 _109200) = (term693 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8217980 B C P a _109200 b p _109198 _109201) (@lem8217979 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217982 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term693 B C P a b p z _109198 h _109199 _109201 _109200) = (term694 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term622 P a _109201 _109200) (term620 B C P _109200 b p _109198 _109201) (term692 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217989 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term695 B C P a b p z _109198 h _109199 _109201 _109200) = (term696 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8215189 (term617 P _109200 b _109201) (term615 B C P p _109198 _109201) (term692 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217990 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term623 P a _109201 _109200) = (term623 P a _109201 _109200).
Proof. exact (eq_refl (term623 P a _109201 _109200)). Qed.
Lemma lem8217993 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term694 B C P a b p z _109198 h _109199 _109201 _109200) = (term697 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8217990 P a _109201 _109200) (@lem8217989 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217994 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term693 B C P a b p z _109198 h _109199 _109201 _109200) = (term697 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217982 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8217993 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217995 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term685 B C P a b p z _109198 h _109199 _109201 _109200) = (term697 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217981 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8217994 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217997 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term670 B C P a b p z _109198 h _109199 _109201 _109200) = (term697 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8217960 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8217995 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8217998 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term697 B C P a b p z _109198 h _109199 _109201 _109200.
Proof. exact (EQ_MP (@lem8217997 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8217897 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8218294 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218295 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8218294 P a i b a' h1). Qed.
Lemma lem8218297 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218298 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8218297 (term579 P a a' i)). Qed.
Lemma lem8218299 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8218298 P a a' i) (@lem8218295 P a i b a' h1)). Qed.
Lemma lem8218301 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218302 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8218301 P a i b a' h1). Qed.
Lemma lem8218304 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218305 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8218304 (term573 P i b a')). Qed.
Lemma lem8218306 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8218305 P i b a') (@lem8218302 P a i b a' h1)). Qed.
Lemma lem8218308 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8217204 B C P p f a') (@lem8217101 B C P p f a' h1)). Qed.
Lemma lem8218309 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term701 B C P p f a'.
Proof. exact (fun h0 : term615 B C P p f a' => @lem8218308 B C P p f a' h1). Qed.
Lemma lem8218311 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218312 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term701 B C P p f a') = (term558 B C P p f a').
Proof. exact (@lem8218311 (term558 B C P p f a')). Qed.
Lemma lem8218313 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8218312 B C P p f a') (@lem8218309 B C P p f a' h1)). Qed.
Lemma lem8218315 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218316 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8218315 P a i b a' h1). Qed.
Lemma lem8218318 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218319 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8218318 (term579 P a a' i)). Qed.
Lemma lem8218320 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8218319 P a a' i) (@lem8218316 P a i b a' h1)). Qed.
Lemma lem8218322 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218323 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8218322 P a i b a' h1). Qed.
Lemma lem8218325 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218326 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8218325 (term573 P i b a')). Qed.
Lemma lem8218327 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8218326 P i b a') (@lem8218323 P a i b a' h1)). Qed.
Lemma lem8218329 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8217222 B C P p g a') (@lem8217107 B C P p g a' h1)). Qed.
Lemma lem8218330 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term701 B C P p g a'.
Proof. exact (fun h0 : term615 B C P p g a' => @lem8218329 B C P p g a' h1). Qed.
Lemma lem8218332 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218333 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term701 B C P p g a') = (term558 B C P p g a').
Proof. exact (@lem8218332 (term558 B C P p g a')). Qed.
Lemma lem8218334 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8218333 B C P p g a') (@lem8218330 B C P p g a' h1)). Qed.
Lemma lem8218336 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218337 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8218336 P a i b a' h1). Qed.
Lemma lem8218339 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218340 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8218339 (term579 P a a' i)). Qed.
Lemma lem8218341 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8218340 P a a' i) (@lem8218337 P a i b a' h1)). Qed.
Lemma lem8218343 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218344 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8218343 P a i b a' h1). Qed.
Lemma lem8218346 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218347 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8218346 (term573 P i b a')). Qed.
Lemma lem8218348 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8218347 P i b a') (@lem8218344 P a i b a' h1)). Qed.
Lemma lem8218350 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8217204 B C P p f a') (@lem8217101 B C P p f a' h1)). Qed.
Lemma lem8218351 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term701 B C P p f a'.
Proof. exact (fun h0 : term615 B C P p f a' => @lem8218350 B C P p f a' h1). Qed.
Lemma lem8218353 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218354 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) : (term701 B C P p f a') = (term558 B C P p f a').
Proof. exact (@lem8218353 (term558 B C P p f a')). Qed.
Lemma lem8218355 {B C P : Type'} (p : type560 B C P) (f : B -> C) (a' : P) (h1 : p f a') : term558 B C P p f a'.
Proof. exact (EQ_MP (@lem8218354 B C P p f a') (@lem8218351 B C P p f a' h1)). Qed.
Lemma lem8218357 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (proj1 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218358 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term698 P a a' i.
Proof. exact (fun h0 : term622 P a a' i => @lem8218357 P a i b a' h1). Qed.
Lemma lem8218360 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218361 {P : Type'} (a : P -> nat) (a' : P) (i : nat) : (term698 P a a' i) = (term579 P a a' i).
Proof. exact (@lem8218360 (term579 P a a' i)). Qed.
Lemma lem8218362 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term579 P a a' i.
Proof. exact (EQ_MP (@lem8218361 P a a' i) (@lem8218358 P a i b a' h1)). Qed.
Lemma lem8218364 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (proj2 (@lem8217327 P a i b a' h1)). Qed.
Lemma lem8218365 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term700 P i b a'.
Proof. exact (fun h0 : term617 P i b a' => @lem8218364 P a i b a' h1). Qed.
Lemma lem8218367 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218368 {P : Type'} (i : nat) (b : P -> nat) (a' : P) : (term700 P i b a') = (term573 P i b a').
Proof. exact (@lem8218367 (term573 P i b a')). Qed.
Lemma lem8218369 {P : Type'} (a : P -> nat) (i : nat) (b : P -> nat) (a' : P) (h1 : term557 P a i b a') : term573 P i b a'.
Proof. exact (EQ_MP (@lem8218368 P i b a') (@lem8218365 P a i b a' h1)). Qed.
Lemma lem8218371 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8217222 B C P p g a') (@lem8217107 B C P p g a' h1)). Qed.
Lemma lem8218372 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term701 B C P p g a'.
Proof. exact (fun h0 : term615 B C P p g a' => @lem8218371 B C P p g a' h1). Qed.
Lemma lem8218374 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8218375 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) : (term701 B C P p g a') = (term558 B C P p g a').
Proof. exact (@lem8218374 (term558 B C P p g a')). Qed.
Lemma lem8218376 {B C P : Type'} (p : type560 B C P) (g : B -> C) (a' : P) (h1 : p g a') : term558 B C P p g a'.
Proof. exact (EQ_MP (@lem8218375 B C P p g a') (@lem8218372 B C P p g a' h1)). Qed.
Lemma lem8218379 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term587 B C P f h g a' i) : term587 B C P f h g a' i.
Proof. exact (h1). Qed.
Lemma lem8218380 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term587 B C P f h g a' i) : term702 B C P f h g a' i.
Proof. exact (fun h0 : (term585 B C P h f a' i) = (term585 B C P h g a' i) => @lem8218379 B C P f h g a' i h1). Qed.
Lemma lem8218382 (p : Prop) : (term703 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem8218383 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (term702 B C P f h g a' i) = (term587 B C P f h g a' i).
Proof. exact (@lem8218382 ((term585 B C P h f a' i) = (term585 B C P h g a' i))). Qed.
Lemma lem8218384 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term587 B C P f h g a' i) : term587 B C P f h g a' i.
Proof. exact (EQ_MP (@lem8218383 B C P f h g a' i) (@lem8218380 B C P f h g a' i h1)). Qed.
Lemma lem8218390 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218391 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term704 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218390 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term705 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218405 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218406 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term706 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term707 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218405 (term615 B C P p _109198 _109201) (term622 P a _109201 _109200) (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218418 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8218419 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term709 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218418 (term622 P a _109201 _109200) (term678 A B C P b p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218423 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218424 {A B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term679 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term710 A B C P b a p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218423 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term711 A B C P p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218435 {A B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term709 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term710 A B C P b a p lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8218419 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8218424 A B C P b a p lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218439 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218440 {A B C P : Type'} (p : type560 B C P) (a : P -> nat) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term712 A B C P a p lt2 z s _109198 h _109199 _109201 _109200) = (term713 A B C P p a lt2 z s _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218439 (term615 B C P p _109199 _109201) (term622 P a _109201 _109200) (term676 A B C P lt2 z s _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218454 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218455 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term714 A B C P a lt2 z s _109198 h _109199 _109201 _109200) = (term715 A B C P lt2 z s a _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218454 (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) (term622 P a _109201 _109200) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8218469 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8218470 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term716 B C P a _109198 h _109199 _109201 _109200) = (term717 B C P _109198 h _109199 a _109201 _109200).
Proof. exact (@lem8218469 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term622 P a _109201 _109200)). Qed.
Lemma lem8218478 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term718 A B C P lt2 z _109198 _109199 _109200 s _109201) = (term718 A B C P lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (eq_refl (term718 A B C P lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8218479 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term715 A B C P lt2 z s a _109198 h _109199 _109201 _109200) = (term719 A B C P lt2 z s _109198 h _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8218478 A B C P lt2 z _109198 _109199 _109200 s _109201) (@lem8218470 B C P _109198 h _109199 a _109201 _109200)). Qed.
Lemma lem8218483 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218484 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (s : P -> A) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term719 A B C P lt2 z s _109198 h _109199 a _109201 _109200) = (term720 A B C P h lt2 z _109198 _109199 s a _109201 _109200).
Proof. exact (@lem8218483 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8218502 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (s : P -> A) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term715 A B C P lt2 z s a _109198 h _109199 _109201 _109200) = (term720 A B C P h lt2 z _109198 _109199 s a _109201 _109200).
Proof. exact (TRANS (@lem8218479 A B C P lt2 z s _109198 h _109199 a _109201 _109200) (@lem8218484 A B C P h lt2 z _109198 _109199 s a _109201 _109200)). Qed.
Lemma lem8218503 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (s : P -> A) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term714 A B C P a lt2 z s _109198 h _109199 _109201 _109200) = (term720 A B C P h lt2 z _109198 _109199 s a _109201 _109200).
Proof. exact (TRANS (@lem8218455 A B C P lt2 z s a _109198 h _109199 _109201 _109200) (@lem8218502 A B C P h lt2 z _109198 _109199 s a _109201 _109200)). Qed.
Lemma lem8218504 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8218505 {A B C P : Type'} (p : type560 B C P) (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (s : P -> A) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term713 A B C P p a lt2 z s _109198 h _109199 _109201 _109200) = (term722 A B C P p h lt2 z _109198 _109199 s a _109201 _109200).
Proof. exact (MK_COMB (@lem8218504 B C P p _109199 _109201) (@lem8218503 A B C P h lt2 z _109198 _109199 s a _109201 _109200)). Qed.
Lemma lem8218509 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218510 {A B C P : Type'} (h : type555 B C P) (p : type560 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (s : P -> A) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term722 A B C P p h lt2 z _109198 _109199 s a _109201 _109200) = (term723 A B C P h p lt2 z _109198 _109199 s a _109201 _109200).
Proof. exact (@lem8218509 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term615 B C P p _109199 _109201) (term724 A B C P lt2 z _109198 _109199 s a _109201 _109200)). Qed.
Lemma lem8218526 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218527 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term725 A B C P p lt2 z _109198 _109199 s a _109201 _109200) = (term726 A B C P lt2 z _109198 s p _109199 a _109201 _109200).
Proof. exact (@lem8218526 (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) (term615 B C P p _109199 _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8218543 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218544 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term723 A B C P h p lt2 z _109198 _109199 s a _109201 _109200) = (term728 A B C P h lt2 z _109198 s p _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8218543 B C P _109198 h _109199 _109201 _109200) (@lem8218527 A B C P lt2 z _109198 s p _109199 a _109201 _109200)). Qed.
Lemma lem8218555 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term722 A B C P p h lt2 z _109198 _109199 s a _109201 _109200) = (term728 A B C P h lt2 z _109198 s p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8218510 A B C P h p lt2 z _109198 _109199 s a _109201 _109200) (@lem8218544 A B C P h lt2 z _109198 s p _109199 a _109201 _109200)). Qed.
Lemma lem8218556 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term713 A B C P p a lt2 z s _109198 h _109199 _109201 _109200) = (term728 A B C P h lt2 z _109198 s p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8218505 A B C P p h lt2 z _109198 _109199 s a _109201 _109200) (@lem8218555 A B C P h lt2 z _109198 s p _109199 a _109201 _109200)). Qed.
Lemma lem8218557 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term712 A B C P a p lt2 z s _109198 h _109199 _109201 _109200) = (term728 A B C P h lt2 z _109198 s p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8218440 A B C P p a lt2 z s _109198 h _109199 _109201 _109200) (@lem8218556 A B C P h lt2 z _109198 s p _109199 a _109201 _109200)). Qed.
Lemma lem8218558 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8218559 {A B C P : Type'} (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term710 A B C P b a p lt2 z s _109198 h _109199 _109201 _109200) = (term729 A B C P b h lt2 z _109198 s p _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8218558 P _109200 b _109201) (@lem8218557 A B C P h lt2 z _109198 s p _109199 a _109201 _109200)). Qed.
Lemma lem8218563 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218564 {A B C P : Type'} (h : type555 B C P) (b : P -> nat) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term729 A B C P b h lt2 z _109198 s p _109199 a _109201 _109200) = (term730 A B C P h b lt2 z _109198 s p _109199 a _109201 _109200).
Proof. exact (@lem8218563 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term617 P _109200 b _109201) (term726 A B C P lt2 z _109198 s p _109199 a _109201 _109200)). Qed.
Lemma lem8218580 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218581 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (b : P -> nat) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term731 A B C P b lt2 z _109198 s p _109199 a _109201 _109200) = (term732 A B C P lt2 z _109198 s b p _109199 a _109201 _109200).
Proof. exact (@lem8218580 (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) (term617 P _109200 b _109201) (term733 B C P p _109199 a _109201 _109200)). Qed.
Lemma lem8218595 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218596 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term734 B C P b p _109199 a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8218595 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8218612 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term718 A B C P lt2 z _109198 _109199 _109200 s _109201) = (term718 A B C P lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (eq_refl (term718 A B C P lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8218613 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term732 A B C P lt2 z _109198 s b p _109199 a _109201 _109200) = (term736 A B C P lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218612 A B C P lt2 z _109198 _109199 _109200 s _109201) (@lem8218596 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8218624 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term731 A B C P b lt2 z _109198 s p _109199 a _109201 _109200) = (term736 A B C P lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218581 A B C P lt2 z _109198 s b p _109199 a _109201 _109200) (@lem8218613 A B C P lt2 z _109198 s p _109199 b a _109201 _109200)). Qed.
Lemma lem8218625 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218626 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term730 A B C P h b lt2 z _109198 s p _109199 a _109201 _109200) = (term737 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218625 B C P _109198 h _109199 _109201 _109200) (@lem8218624 A B C P lt2 z _109198 s p _109199 b a _109201 _109200)). Qed.
Lemma lem8218637 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term729 A B C P b h lt2 z _109198 s p _109199 a _109201 _109200) = (term737 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218564 A B C P h b lt2 z _109198 s p _109199 a _109201 _109200) (@lem8218626 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200)). Qed.
Lemma lem8218638 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term710 A B C P b a p lt2 z s _109198 h _109199 _109201 _109200) = (term737 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218559 A B C P b h lt2 z _109198 s p _109199 a _109201 _109200) (@lem8218637 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200)). Qed.
Lemma lem8218639 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term709 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term737 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218435 A B C P b a p lt2 z s _109198 h _109199 _109201 _109200) (@lem8218638 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200)). Qed.
Lemma lem8218640 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8218641 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term707 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term738 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218640 B C P p _109198 _109201) (@lem8218639 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200)). Qed.
Lemma lem8218645 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218646 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (s : P -> A) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term738 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200) = (term739 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200).
Proof. exact (@lem8218645 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term615 B C P p _109198 _109201) (term736 A B C P lt2 z _109198 s p _109199 b a _109201 _109200)). Qed.
Lemma lem8218662 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218663 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term740 A B C P lt2 z _109198 s p _109199 b a _109201 _109200) = (term741 A B C P lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8218662 (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) (term615 B C P p _109198 _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8218699 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218700 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term739 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218699 B C P _109198 h _109199 _109201 _109200) (@lem8218663 A B C P lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218711 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term738 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218646 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200) (@lem8218700 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218712 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term707 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218641 A B C P h lt2 z _109198 s p _109199 b a _109201 _109200) (@lem8218711 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218713 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term706 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218406 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8218712 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218714 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8218715 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term704 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term743 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218714 P _109200 b _109201) (@lem8218713 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218719 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218720 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term743 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) = (term744 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8218719 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term617 P _109200 b _109201) (term741 A B C P lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218736 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218737 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term745 A B C P lt2 z s _109198 p _109199 b a _109201 _109200) = (term746 A B C P lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8218736 (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) (term617 P _109200 b _109201) (term747 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218751 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218752 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term749 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8218751 (term615 B C P p _109198 _109201) (term617 P _109200 b _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8218766 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218767 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term751 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8218766 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term752 P b a _109201 _109200)). Qed.
Lemma lem8218779 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8218780 {P : Type'} (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term753 P b a _109201 _109200) = (term752 P b a _109201 _109200).
Proof. exact (@lem8218779 (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8218786 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8218787 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term751 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218786 B C P p _109199 _109201) (@lem8218780 P b a _109201 _109200)). Qed.
Lemma lem8218798 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218767 B C P p _109199 b a _109201 _109200) (@lem8218787 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8218799 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8218800 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term749 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218799 B C P p _109198 _109201) (@lem8218798 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8218811 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218752 B C P _109198 p _109199 b a _109201 _109200) (@lem8218800 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218812 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term718 A B C P lt2 z _109198 _109199 _109200 s _109201) = (term718 A B C P lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (eq_refl (term718 A B C P lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8218813 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term746 A B C P lt2 z s _109198 p _109199 b a _109201 _109200) = (term741 A B C P lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218812 A B C P lt2 z _109198 _109199 _109200 s _109201) (@lem8218811 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218824 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term745 A B C P lt2 z s _109198 p _109199 b a _109201 _109200) = (term741 A B C P lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218737 A B C P lt2 z s _109198 p _109199 b a _109201 _109200) (@lem8218813 A B C P lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218825 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218826 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term744 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218825 B C P _109198 h _109199 _109201 _109200) (@lem8218824 A B C P lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218837 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term743 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218720 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) (@lem8218826 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218838 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term704 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218715 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) (@lem8218837 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218839 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218391 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) (@lem8218838 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8218841 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term754 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term755 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218840) (@lem8218839 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8218855 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218856 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term756 B C P a b p _109198 h _109199 _109201 _109200) = (term757 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218855 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term758 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218870 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218871 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term759 B C P a b p _109198 h _109199 _109201 _109200) = (term760 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218870 (term615 B C P p _109198 _109201) (term622 P a _109201 _109200) (term761 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218883 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8218884 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term762 B C P a b p _109198 h _109199 _109201 _109200) = (term761 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218883 (term622 P a _109201 _109200) (term763 B C P b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218888 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218889 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term761 B C P a b p _109198 h _109199 _109201 _109200) = (term764 B C P b a p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218888 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term765 B C P p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218900 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term762 B C P a b p _109198 h _109199 _109201 _109200) = (term764 B C P b a p _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8218884 B C P a b p _109198 h _109199 _109201 _109200) (@lem8218889 B C P b a p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218904 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218905 {B C P : Type'} (p : type560 B C P) (a : P -> nat) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term766 B C P a p _109198 h _109199 _109201 _109200) = (term767 B C P p a _109198 h _109199 _109201 _109200).
Proof. exact (@lem8218904 (term615 B C P p _109199 _109201) (term622 P a _109201 _109200) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8218919 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8218920 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term716 B C P a _109198 h _109199 _109201 _109200) = (term717 B C P _109198 h _109199 a _109201 _109200).
Proof. exact (@lem8218919 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term622 P a _109201 _109200)). Qed.
Lemma lem8218928 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8218929 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term767 B C P p a _109198 h _109199 _109201 _109200) = (term768 B C P p _109198 h _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8218928 B C P p _109199 _109201) (@lem8218920 B C P _109198 h _109199 a _109201 _109200)). Qed.
Lemma lem8218933 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218934 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term768 B C P p _109198 h _109199 a _109201 _109200) = (term769 B C P _109198 h p _109199 a _109201 _109200).
Proof. exact (@lem8218933 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term615 B C P p _109199 _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8218952 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term767 B C P p a _109198 h _109199 _109201 _109200) = (term769 B C P _109198 h p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8218929 B C P p _109198 h _109199 a _109201 _109200) (@lem8218934 B C P _109198 h p _109199 a _109201 _109200)). Qed.
Lemma lem8218953 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term766 B C P a p _109198 h _109199 _109201 _109200) = (term769 B C P _109198 h p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8218905 B C P p a _109198 h _109199 _109201 _109200) (@lem8218952 B C P _109198 h p _109199 a _109201 _109200)). Qed.
Lemma lem8218954 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8218955 {B C P : Type'} (b : P -> nat) (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term764 B C P b a p _109198 h _109199 _109201 _109200) = (term770 B C P b _109198 h p _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8218954 P _109200 b _109201) (@lem8218953 B C P _109198 h p _109199 a _109201 _109200)). Qed.
Lemma lem8218959 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218960 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (b : P -> nat) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term770 B C P b _109198 h p _109199 a _109201 _109200) = (term771 B C P _109198 h b p _109199 a _109201 _109200).
Proof. exact (@lem8218959 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term617 P _109200 b _109201) (term733 B C P p _109199 a _109201 _109200)). Qed.
Lemma lem8218976 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8218977 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term734 B C P b p _109199 a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8218976 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8218993 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8218994 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term771 B C P _109198 h b p _109199 a _109201 _109200) = (term772 B C P _109198 h p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8218993 B C P _109198 h _109199 _109201 _109200) (@lem8218977 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219005 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term770 B C P b _109198 h p _109199 a _109201 _109200) = (term772 B C P _109198 h p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218960 B C P _109198 h b p _109199 a _109201 _109200) (@lem8218994 B C P _109198 h p _109199 b a _109201 _109200)). Qed.
Lemma lem8219006 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term764 B C P b a p _109198 h _109199 _109201 _109200) = (term772 B C P _109198 h p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218955 B C P b _109198 h p _109199 a _109201 _109200) (@lem8219005 B C P _109198 h p _109199 b a _109201 _109200)). Qed.
Lemma lem8219007 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term762 B C P a b p _109198 h _109199 _109201 _109200) = (term772 B C P _109198 h p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218900 B C P b a p _109198 h _109199 _109201 _109200) (@lem8219006 B C P _109198 h p _109199 b a _109201 _109200)). Qed.
Lemma lem8219008 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8219009 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term760 B C P a b p _109198 h _109199 _109201 _109200) = (term773 B C P _109198 h p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219008 B C P p _109198 _109201) (@lem8219007 B C P _109198 h p _109199 b a _109201 _109200)). Qed.
Lemma lem8219013 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219014 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term773 B C P _109198 h p _109199 b a _109201 _109200) = (term774 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219013 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term615 B C P p _109198 _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219052 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term760 B C P a b p _109198 h _109199 _109201 _109200) = (term774 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219009 B C P _109198 h p _109199 b a _109201 _109200) (@lem8219014 B C P h _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219053 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term759 B C P a b p _109198 h _109199 _109201 _109200) = (term774 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218871 B C P a b p _109198 h _109199 _109201 _109200) (@lem8219052 B C P h _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219054 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8219055 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term757 B C P a b p _109198 h _109199 _109201 _109200) = (term775 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219054 P _109200 b _109201) (@lem8219053 B C P h _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219059 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219060 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term775 B C P h _109198 p _109199 b a _109201 _109200) = (term776 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219059 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term617 P _109200 b _109201) (term747 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219076 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219077 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term749 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219076 (term615 B C P p _109198 _109201) (term617 P _109200 b _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219091 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219092 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term751 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8219091 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term752 P b a _109201 _109200)). Qed.
Lemma lem8219104 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8219105 {P : Type'} (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term753 P b a _109201 _109200) = (term752 P b a _109201 _109200).
Proof. exact (@lem8219104 (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219111 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8219112 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term751 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219111 B C P p _109199 _109201) (@lem8219105 P b a _109201 _109200)). Qed.
Lemma lem8219123 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219092 B C P p _109199 b a _109201 _109200) (@lem8219112 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219124 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8219125 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term749 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219124 B C P p _109198 _109201) (@lem8219123 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219136 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219077 B C P _109198 p _109199 b a _109201 _109200) (@lem8219125 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219137 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219138 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term776 B C P h _109198 p _109199 b a _109201 _109200) = (term774 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219137 B C P _109198 h _109199 _109201 _109200) (@lem8219136 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219149 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term775 B C P h _109198 p _109199 b a _109201 _109200) = (term774 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219060 B C P h _109198 p _109199 b a _109201 _109200) (@lem8219138 B C P h _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219150 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term757 B C P a b p _109198 h _109199 _109201 _109200) = (term774 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219055 B C P h _109198 p _109199 b a _109201 _109200) (@lem8219149 B C P h _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219151 {B C P : Type'} (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term756 B C P a b p _109198 h _109199 _109201 _109200) = (term774 B C P h _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8218856 B C P a b p _109198 h _109199 _109201 _109200) (@lem8219150 B C P h _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219152 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term718 A B C P lt2 z _109198 _109199 _109200 s _109201) = (term718 A B C P lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (eq_refl (term718 A B C P lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8219153 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (h : type555 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200) = (term778 A B C P lt2 z s h _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219152 A B C P lt2 z _109198 _109199 _109200 s _109201) (@lem8219151 B C P h _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219157 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219158 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term778 A B C P lt2 z s h _109198 p _109199 b a _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219157 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) (term747 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219206 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219153 A B C P lt2 z s h _109198 p _109199 b a _109201 _109200) (@lem8219158 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219207 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : ((term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200)) = ((term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)).
Proof. exact (MK_COMB (@lem8218841 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) (@lem8219206 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219209 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8219210 (x : Prop) : (x = x) = True.
Proof. exact (@lem8219209 Prop x). Qed.
Lemma lem8219211 {A B C P : Type'} (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : ((term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) = (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)) = True.
Proof. exact (@lem8219210 (term742 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219212 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : ((term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200)) = True.
Proof. exact (TRANS (@lem8219207 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200) (@lem8219211 A B C P h lt2 z s _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219213 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : True = ((term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200)).
Proof. exact (SYM (@lem8219212 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219214 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (s : P -> A) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term684 A B C P a b p lt2 z s _109198 h _109199 _109201 _109200) = (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200).
Proof. exact (EQ_MP (@lem8219213 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200) (@lem0)). Qed.
Lemma lem8219215 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200.
Proof. exact (EQ_MP (@lem8219214 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200) (@lem8217956 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8219217 (b : Prop) (a : Prop) : (a \/ b) = (term779 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8219218 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200) = (term780 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (@lem8219217 (term756 B C P a b p _109198 h _109199 _109201 _109200) (term609 A B C P lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8219220 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8219221 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term783 B C P a b p _109198 h _109199 _109201 _109200) = (term784 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219220 (term622 P a _109201 _109200) (term785 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219223 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8219224 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term786 P a _109201 _109200) = (term579 P a _109201 _109200).
Proof. exact (@lem8219223 (term579 P a _109201 _109200)). Qed.
Lemma lem8219225 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8219226 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term787 P a _109201 _109200) = (term581 P a _109201 _109200).
Proof. exact (MK_COMB (@lem8219225) (@lem8219224 P a _109201 _109200)). Qed.
Lemma lem8219228 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8219229 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term788 B C P a b p _109198 h _109199 _109201 _109200) = (term789 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219228 (term617 P _109200 b _109201) (term758 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219231 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8219232 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term790 P _109200 b _109201) = (term573 P _109200 b _109201).
Proof. exact (@lem8219231 (term573 P _109200 b _109201)). Qed.
Lemma lem8219233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8219234 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term791 P _109200 b _109201) = (term792 P _109200 b _109201).
Proof. exact (MK_COMB (@lem8219233) (@lem8219232 P _109200 b _109201)). Qed.
Lemma lem8219236 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8219237 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term793 B C P a b p _109198 h _109199 _109201 _109200) = (term794 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219236 (term615 B C P p _109198 _109201) (term761 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219239 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8219240 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term795 B C P p _109198 _109201) = (term558 B C P p _109198 _109201).
Proof. exact (@lem8219239 (term558 B C P p _109198 _109201)). Qed.
Lemma lem8219241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8219242 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term796 B C P p _109198 _109201) = (term797 B C P p _109198 _109201).
Proof. exact (MK_COMB (@lem8219241) (@lem8219240 B C P p _109198 _109201)). Qed.
Lemma lem8219244 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8219245 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term798 B C P a b p _109198 h _109199 _109201 _109200) = (term799 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219244 (term622 P a _109201 _109200) (term763 B C P b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219247 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8219248 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term786 P a _109201 _109200) = (term579 P a _109201 _109200).
Proof. exact (@lem8219247 (term579 P a _109201 _109200)). Qed.
Lemma lem8219249 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8219250 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term787 P a _109201 _109200) = (term581 P a _109201 _109200).
Proof. exact (MK_COMB (@lem8219249) (@lem8219248 P a _109201 _109200)). Qed.
Lemma lem8219252 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8219253 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term800 B C P b p _109198 h _109199 _109201 _109200) = (term801 B C P b p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219252 (term617 P _109200 b _109201) (term765 B C P p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219255 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8219256 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term790 P _109200 b _109201) = (term573 P _109200 b _109201).
Proof. exact (@lem8219255 (term573 P _109200 b _109201)). Qed.
Lemma lem8219257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8219258 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term791 P _109200 b _109201) = (term792 P _109200 b _109201).
Proof. exact (MK_COMB (@lem8219257) (@lem8219256 P _109200 b _109201)). Qed.
Lemma lem8219260 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8219261 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term802 B C P p _109198 h _109199 _109201 _109200) = (term803 B C P p _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219260 (term615 B C P p _109199 _109201) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8219263 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8219264 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term795 B C P p _109199 _109201) = (term558 B C P p _109199 _109201).
Proof. exact (@lem8219263 (term558 B C P p _109199 _109201)). Qed.
Lemma lem8219265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8219266 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term796 B C P p _109199 _109201) = (term797 B C P p _109199 _109201).
Proof. exact (MK_COMB (@lem8219265) (@lem8219264 B C P p _109199 _109201)). Qed.
Lemma lem8219267 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term587 B C P _109198 h _109199 _109201 _109200) = (term587 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term587 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219268 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term803 B C P p _109198 h _109199 _109201 _109200) = (term804 B C P p _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8219266 B C P p _109199 _109201) (@lem8219267 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219269 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term802 B C P p _109198 h _109199 _109201 _109200) = (term804 B C P p _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8219261 B C P p _109198 h _109199 _109201 _109200) (@lem8219268 B C P p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219270 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term801 B C P b p _109198 h _109199 _109201 _109200) = (term805 B C P b p _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8219258 P _109200 b _109201) (@lem8219269 B C P p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219271 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term800 B C P b p _109198 h _109199 _109201 _109200) = (term805 B C P b p _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8219253 B C P b p _109198 h _109199 _109201 _109200) (@lem8219270 B C P b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219272 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term799 B C P a b p _109198 h _109199 _109201 _109200) = (term806 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8219250 P a _109201 _109200) (@lem8219271 B C P b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219273 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term798 B C P a b p _109198 h _109199 _109201 _109200) = (term806 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8219245 B C P a b p _109198 h _109199 _109201 _109200) (@lem8219272 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219274 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term794 B C P a b p _109198 h _109199 _109201 _109200) = (term807 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8219242 B C P p _109198 _109201) (@lem8219273 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219275 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term793 B C P a b p _109198 h _109199 _109201 _109200) = (term807 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8219237 B C P a b p _109198 h _109199 _109201 _109200) (@lem8219274 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219276 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term789 B C P a b p _109198 h _109199 _109201 _109200) = (term808 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8219234 P _109200 b _109201) (@lem8219275 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219277 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term788 B C P a b p _109198 h _109199 _109201 _109200) = (term808 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8219229 B C P a b p _109198 h _109199 _109201 _109200) (@lem8219276 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219278 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term784 B C P a b p _109198 h _109199 _109201 _109200) = (term809 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8219226 P a _109201 _109200) (@lem8219277 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219279 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term783 B C P a b p _109198 h _109199 _109201 _109200) = (term809 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8219221 B C P a b p _109198 h _109199 _109201 _109200) (@lem8219278 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8219281 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term810 B C P a b p _109198 h _109199 _109201 _109200) = (term811 B C P a b p _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8219280) (@lem8219279 B C P a b p _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219282 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term609 A B C P lt2 z _109198 _109199 _109200 s _109201) = (term609 A B C P lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (eq_refl (term609 A B C P lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8219283 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term780 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201) = (term812 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (MK_COMB (@lem8219281 B C P a b p _109198 h _109199 _109201 _109200) (@lem8219282 A B C P lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8219284 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (h : type555 B C P) (lt2 : type1470 A B) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (s : P -> A) (_109201 : P) : (term777 A B C P lt2 z s a b p _109198 h _109199 _109201 _109200) = (term812 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201).
Proof. exact (TRANS (@lem8219218 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201) (@lem8219283 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201)). Qed.
Lemma lem8219286 {B C P : Type'} (f : B -> C) (h : type555 B C P) (i : nat) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : p g a') : term804 B C P p f h g a' i.
Proof. exact (conj (@lem8218376 B C P p g a' h2) (@lem8218384 B C P f h g a' i h1)). Qed.
Lemma lem8219287 {B C P : Type'} (f : B -> C) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p g a') : term805 B C P b p f h g a' i.
Proof. exact (conj (@lem8218369 P a i b a' h2) (@lem8219286 B C P f h i p g a' h1 h3)). Qed.
Lemma lem8219288 {B C P : Type'} (f : B -> C) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p g a') : term806 B C P a b p f h g a' i.
Proof. exact (conj (@lem8218362 P a i b a' h2) (@lem8219287 B C P f h a i b p g a' h1 h2 h3)). Qed.
Lemma lem8219289 {B C P : Type'} (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p f a') (h4 : p g a') : term807 B C P a b p f h g a' i.
Proof. exact (conj (@lem8218355 B C P p f a' h3) (@lem8219288 B C P f h a i b p g a' h1 h2 h4)). Qed.
Lemma lem8219290 {B C P : Type'} (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p f a') (h4 : p g a') : term808 B C P a b p f h g a' i.
Proof. exact (conj (@lem8218348 P a i b a' h2) (@lem8219289 B C P h a i b f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8219291 {B C P : Type'} (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term587 B C P f h g a' i) (h2 : term557 P a i b a') (h3 : p f a') (h4 : p g a') : term809 B C P a b p f h g a' i.
Proof. exact (conj (@lem8218341 P a i b a' h2) (@lem8219290 B C P h a i b f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8219293 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term812 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201.
Proof. exact (EQ_MP (@lem8219284 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201) (@lem8219215 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8219294 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term812 A B C P a b p h lt2 z _109198 _109199 _109200 s _109201.
Proof. exact (@lem8219293 A B C P _109198 _109199 _109200 _109201 a b p lt2 s z h h1). Qed.
Lemma lem8219295 {A B C P : Type'} (f : B -> C) (g : B -> C) (i : nat) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term812 A B C P a b p h lt2 z f g i s a'.
Proof. exact (@lem8219294 A B C P f g i a' a b p lt2 s z h h1). Qed.
Lemma lem8219298 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term550 A B C P a b p lt2 s z h) (h2 : term587 B C P f h g a' i) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term609 A B C P lt2 z f g i s a'.
Proof. exact (@lem8219295 A B C P f g i a' a b p lt2 s z h h1 (@lem8219291 B C P h a i b f p g a' h2 h3 h4 h5)). Qed.
Lemma lem8219299 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term550 A B C P a b p lt2 s z h) (h2 : term587 B C P f h g a' i) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term813 A B C P lt2 z f g i s a'.
Proof. exact (fun h0 : term814 A B C P lt2 z f g i s a' => @lem8219298 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5). Qed.
Lemma lem8219301 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8219302 {A B C P : Type'} (lt2 : type1470 A B) (z : type521 B C P) (f : B -> C) (g : B -> C) (i : nat) (s : P -> A) (a' : P) : (term813 A B C P lt2 z f g i s a') = (term609 A B C P lt2 z f g i s a').
Proof. exact (@lem8219301 (term609 A B C P lt2 z f g i s a')). Qed.
Lemma lem8219303 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term550 A B C P a b p lt2 s z h) (h2 : term587 B C P f h g a' i) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term609 A B C P lt2 z f g i s a'.
Proof. exact (EQ_MP (@lem8219302 A B C P lt2 z f g i s a') (@lem8219299 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5)). Qed.
Lemma lem8219309 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8219310 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : (term568 A B C P lt2 s a' f g _109197) = (term815 A B C P f g lt2 _109197 s a').
Proof. exact (@lem8219309 ((@I (B -> C) f _109197) = (@I (B -> C) g _109197)) (term565 A B P lt2 _109197 s a')). Qed.
Lemma lem8219318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8219319 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : (term816 A B C P lt2 s a' f g _109197) = (term817 A B C P f g lt2 _109197 s a').
Proof. exact (MK_COMB (@lem8219318) (@lem8219310 A B C P f g lt2 _109197 s a')). Qed.
Lemma lem8219327 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : (term815 A B C P f g lt2 _109197 s a') = (term815 A B C P f g lt2 _109197 s a').
Proof. exact (eq_refl (term815 A B C P f g lt2 _109197 s a')). Qed.
Lemma lem8219328 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : ((term568 A B C P lt2 s a' f g _109197) = (term815 A B C P f g lt2 _109197 s a')) = ((term815 A B C P f g lt2 _109197 s a') = (term815 A B C P f g lt2 _109197 s a')).
Proof. exact (MK_COMB (@lem8219319 A B C P f g lt2 _109197 s a') (@lem8219327 A B C P f g lt2 _109197 s a')). Qed.
Lemma lem8219330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8219331 (x : Prop) : (x = x) = True.
Proof. exact (@lem8219330 Prop x). Qed.
Lemma lem8219332 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : ((term815 A B C P f g lt2 _109197 s a') = (term815 A B C P f g lt2 _109197 s a')) = True.
Proof. exact (@lem8219331 (term815 A B C P f g lt2 _109197 s a')). Qed.
Lemma lem8219333 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : ((term568 A B C P lt2 s a' f g _109197) = (term815 A B C P f g lt2 _109197 s a')) = True.
Proof. exact (TRANS (@lem8219328 A B C P f g lt2 _109197 s a') (@lem8219332 A B C P f g lt2 _109197 s a')). Qed.
Lemma lem8219334 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : True = ((term568 A B C P lt2 s a' f g _109197) = (term815 A B C P f g lt2 _109197 s a')).
Proof. exact (SYM (@lem8219333 A B C P f g lt2 _109197 s a')). Qed.
Lemma lem8219335 {A B C P : Type'} (f : B -> C) (g : B -> C) (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : (term568 A B C P lt2 s a' f g _109197) = (term815 A B C P f g lt2 _109197 s a').
Proof. exact (EQ_MP (@lem8219334 A B C P f g lt2 _109197 s a') (@lem0)). Qed.
Lemma lem8219336 {A B C P : Type'} (_109197 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term815 A B C P f g lt2 _109197 s a'.
Proof. exact (EQ_MP (@lem8219335 A B C P f g lt2 _109197 s a') (@lem8217908 A B C P _109197 lt2 s a' f g h1)). Qed.
Lemma lem8219338 (b : Prop) (a : Prop) : (a \/ b) = (term779 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8219339 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109197 : B) : (term815 A B C P f g lt2 _109197 s a') = (term818 A B C P lt2 s a' f g _109197).
Proof. exact (@lem8219338 (term565 A B P lt2 _109197 s a') ((@I (B -> C) f _109197) = (@I (B -> C) g _109197))). Qed.
Lemma lem8219341 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8219342 {A B P : Type'} (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : (term819 A B P lt2 _109197 s a') = (term563 A B P lt2 _109197 s a').
Proof. exact (@lem8219341 (term563 A B P lt2 _109197 s a')). Qed.
Lemma lem8219343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8219344 {A B P : Type'} (lt2 : type1470 A B) (_109197 : B) (s : P -> A) (a' : P) : (term820 A B P lt2 _109197 s a') = (term821 A B P lt2 _109197 s a').
Proof. exact (MK_COMB (@lem8219343) (@lem8219342 A B P lt2 _109197 s a')). Qed.
Lemma lem8219345 {B C : Type'} (f : B -> C) (g : B -> C) (_109197 : B) : ((@I (B -> C) f _109197) = (@I (B -> C) g _109197)) = ((@I (B -> C) f _109197) = (@I (B -> C) g _109197)).
Proof. exact (eq_refl ((@I (B -> C) f _109197) = (@I (B -> C) g _109197))). Qed.
Lemma lem8219346 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109197 : B) : (term818 A B C P lt2 s a' f g _109197) = (term822 A B C P lt2 s a' f g _109197).
Proof. exact (MK_COMB (@lem8219344 A B P lt2 _109197 s a') (@lem8219345 B C f g _109197)). Qed.
Lemma lem8219347 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (_109197 : B) : (term815 A B C P f g lt2 _109197 s a') = (term822 A B C P lt2 s a' f g _109197).
Proof. exact (TRANS (@lem8219339 A B C P lt2 s a' f g _109197) (@lem8219346 A B C P lt2 s a' f g _109197)). Qed.
Lemma lem8219350 {A B C P : Type'} (_109197 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term822 A B C P lt2 s a' f g _109197.
Proof. exact (EQ_MP (@lem8219347 A B C P lt2 s a' f g _109197) (@lem8219336 A B C P _109197 lt2 s a' f g h1)). Qed.
Lemma lem8219351 {A B C P : Type'} (_109197 : B) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term822 A B C P lt2 s a' f g _109197.
Proof. exact (@lem8219350 A B C P _109197 lt2 s a' f g h1). Qed.
Lemma lem8219352 {A B C P : Type'} (z : type521 B C P) (i : nat) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term174 A B C P lt2 s a' f g) : term823 A B C P lt2 s z f g i a'.
Proof. exact (@lem8219351 A B C P (term592 B C P z f g i a') lt2 s a' f g h1). Qed.
Lemma lem8219355 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term595 B C P z f g i a') = (term598 B C P z f g i a').
Proof. exact (@lem8219352 A B C P z i lt2 s a' f g h1 (@lem8219303 A B C P lt2 s z h a i b f p g a' h2 h3 h4 h5 h6)). Qed.
Lemma lem8219356 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term824 B C P z f g i a'.
Proof. exact (fun h0 : term602 B C P z f g i a' => @lem8219355 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem8219358 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8219359 {B C P : Type'} (z : type521 B C P) (f : B -> C) (g : B -> C) (i : nat) (a' : P) : (term824 B C P z f g i a') = ((term595 B C P z f g i a') = (term598 B C P z f g i a')).
Proof. exact (@lem8219358 ((term595 B C P z f g i a') = (term598 B C P z f g i a'))). Qed.
Lemma lem8219360 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term595 B C P z f g i a') = (term598 B C P z f g i a').
Proof. exact (EQ_MP (@lem8219359 B C P z f g i a') (@lem8219356 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8219366 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219367 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term697 B C P a b p z _109198 h _109199 _109201 _109200) = (term825 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219366 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term826 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219381 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219382 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term827 B C P a b p z _109198 h _109199 _109201 _109200) = (term828 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219381 (term615 B C P p _109198 _109201) (term622 P a _109201 _109200) (term692 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219394 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8219395 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term829 B C P a b p z _109198 h _109199 _109201 _109200) = (term692 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219394 (term622 P a _109201 _109200) (term691 B C P b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219399 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219400 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term692 B C P a b p z _109198 h _109199 _109201 _109200) = (term830 B C P b a p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219399 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term831 B C P p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219411 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term829 B C P a b p z _109198 h _109199 _109201 _109200) = (term830 B C P b a p z _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8219395 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8219400 B C P b a p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219415 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219416 {B C P : Type'} (p : type560 B C P) (a : P -> nat) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term832 B C P a p z _109198 h _109199 _109201 _109200) = (term833 B C P p a z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219415 (term615 B C P p _109199 _109201) (term622 P a _109201 _109200) (term689 B C P z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219430 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219431 {B C P : Type'} (z : type521 B C P) (a : P -> nat) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term834 B C P a z _109198 h _109199 _109201 _109200) = (term835 B C P z a _109198 h _109199 _109201 _109200).
Proof. exact (@lem8219430 (term602 B C P z _109198 _109199 _109200 _109201) (term622 P a _109201 _109200) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8219447 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8219448 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term716 B C P a _109198 h _109199 _109201 _109200) = (term717 B C P _109198 h _109199 a _109201 _109200).
Proof. exact (@lem8219447 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term622 P a _109201 _109200)). Qed.
Lemma lem8219456 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term836 B C P z _109198 _109199 _109200 _109201) = (term836 B C P z _109198 _109199 _109200 _109201).
Proof. exact (eq_refl (term836 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219457 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term835 B C P z a _109198 h _109199 _109201 _109200) = (term837 B C P z _109198 h _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8219456 B C P z _109198 _109199 _109200 _109201) (@lem8219448 B C P _109198 h _109199 a _109201 _109200)). Qed.
Lemma lem8219461 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219462 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term837 B C P z _109198 h _109199 a _109201 _109200) = (term838 B C P h z _109198 _109199 a _109201 _109200).
Proof. exact (@lem8219461 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term602 B C P z _109198 _109199 _109200 _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219482 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term835 B C P z a _109198 h _109199 _109201 _109200) = (term838 B C P h z _109198 _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8219457 B C P z _109198 h _109199 a _109201 _109200) (@lem8219462 B C P h z _109198 _109199 a _109201 _109200)). Qed.
Lemma lem8219483 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term834 B C P a z _109198 h _109199 _109201 _109200) = (term838 B C P h z _109198 _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8219431 B C P z a _109198 h _109199 _109201 _109200) (@lem8219482 B C P h z _109198 _109199 a _109201 _109200)). Qed.
Lemma lem8219484 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8219485 {B C P : Type'} (p : type560 B C P) (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term833 B C P p a z _109198 h _109199 _109201 _109200) = (term839 B C P p h z _109198 _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8219484 B C P p _109199 _109201) (@lem8219483 B C P h z _109198 _109199 a _109201 _109200)). Qed.
Lemma lem8219489 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219490 {B C P : Type'} (h : type555 B C P) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term839 B C P p h z _109198 _109199 a _109201 _109200) = (term840 B C P h p z _109198 _109199 a _109201 _109200).
Proof. exact (@lem8219489 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term615 B C P p _109199 _109201) (term841 B C P z _109198 _109199 a _109201 _109200)). Qed.
Lemma lem8219506 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219507 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term842 B C P p z _109198 _109199 a _109201 _109200) = (term843 B C P z _109198 p _109199 a _109201 _109200).
Proof. exact (@lem8219506 (term602 B C P z _109198 _109199 _109200 _109201) (term615 B C P p _109199 _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219525 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219526 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term840 B C P h p z _109198 _109199 a _109201 _109200) = (term844 B C P h z _109198 p _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8219525 B C P _109198 h _109199 _109201 _109200) (@lem8219507 B C P z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219537 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term839 B C P p h z _109198 _109199 a _109201 _109200) = (term844 B C P h z _109198 p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8219490 B C P h p z _109198 _109199 a _109201 _109200) (@lem8219526 B C P h z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219538 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term833 B C P p a z _109198 h _109199 _109201 _109200) = (term844 B C P h z _109198 p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8219485 B C P p h z _109198 _109199 a _109201 _109200) (@lem8219537 B C P h z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219539 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term832 B C P a p z _109198 h _109199 _109201 _109200) = (term844 B C P h z _109198 p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8219416 B C P p a z _109198 h _109199 _109201 _109200) (@lem8219538 B C P h z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219540 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8219541 {B C P : Type'} (b : P -> nat) (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term830 B C P b a p z _109198 h _109199 _109201 _109200) = (term845 B C P b h z _109198 p _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8219540 P _109200 b _109201) (@lem8219539 B C P h z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219545 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219546 {B C P : Type'} (h : type555 B C P) (b : P -> nat) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term845 B C P b h z _109198 p _109199 a _109201 _109200) = (term846 B C P h b z _109198 p _109199 a _109201 _109200).
Proof. exact (@lem8219545 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term617 P _109200 b _109201) (term843 B C P z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219562 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219563 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (b : P -> nat) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term847 B C P b z _109198 p _109199 a _109201 _109200) = (term848 B C P z _109198 b p _109199 a _109201 _109200).
Proof. exact (@lem8219562 (term602 B C P z _109198 _109199 _109200 _109201) (term617 P _109200 b _109201) (term733 B C P p _109199 a _109201 _109200)). Qed.
Lemma lem8219579 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219580 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term734 B C P b p _109199 a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8219579 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219596 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term836 B C P z _109198 _109199 _109200 _109201) = (term836 B C P z _109198 _109199 _109200 _109201).
Proof. exact (eq_refl (term836 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219597 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term848 B C P z _109198 b p _109199 a _109201 _109200) = (term849 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219596 B C P z _109198 _109199 _109200 _109201) (@lem8219580 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219608 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term847 B C P b z _109198 p _109199 a _109201 _109200) = (term849 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219563 B C P z _109198 b p _109199 a _109201 _109200) (@lem8219597 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219609 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219610 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term846 B C P h b z _109198 p _109199 a _109201 _109200) = (term850 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219609 B C P _109198 h _109199 _109201 _109200) (@lem8219608 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219621 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term845 B C P b h z _109198 p _109199 a _109201 _109200) = (term850 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219546 B C P h b z _109198 p _109199 a _109201 _109200) (@lem8219610 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219622 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term830 B C P b a p z _109198 h _109199 _109201 _109200) = (term850 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219541 B C P b h z _109198 p _109199 a _109201 _109200) (@lem8219621 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219623 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term829 B C P a b p z _109198 h _109199 _109201 _109200) = (term850 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219411 B C P b a p z _109198 h _109199 _109201 _109200) (@lem8219622 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219624 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8219625 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term828 B C P a b p z _109198 h _109199 _109201 _109200) = (term851 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219624 B C P p _109198 _109201) (@lem8219623 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219629 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219630 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term851 B C P h z _109198 p _109199 b a _109201 _109200) = (term852 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219629 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term615 B C P p _109198 _109201) (term849 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219646 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219647 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term853 B C P z _109198 p _109199 b a _109201 _109200) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219646 (term602 B C P z _109198 _109199 _109200 _109201) (term615 B C P p _109198 _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219685 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219686 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term852 B C P h z _109198 p _109199 b a _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219685 B C P _109198 h _109199 _109201 _109200) (@lem8219647 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219697 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term851 B C P h z _109198 p _109199 b a _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219630 B C P h z _109198 p _109199 b a _109201 _109200) (@lem8219686 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219698 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term828 B C P a b p z _109198 h _109199 _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219625 B C P h z _109198 p _109199 b a _109201 _109200) (@lem8219697 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219699 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term827 B C P a b p z _109198 h _109199 _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219382 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8219698 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219700 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8219701 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term825 B C P a b p z _109198 h _109199 _109201 _109200) = (term856 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219700 P _109200 b _109201) (@lem8219699 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219705 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219706 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term856 B C P h z _109198 p _109199 b a _109201 _109200) = (term857 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219705 ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) (term617 P _109200 b _109201) (term854 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219722 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219723 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term858 B C P z _109198 p _109199 b a _109201 _109200) = (term859 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219722 (term602 B C P z _109198 _109199 _109200 _109201) (term617 P _109200 b _109201) (term747 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219739 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219740 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term749 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8219739 (term615 B C P p _109198 _109201) (term617 P _109200 b _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219754 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219755 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term751 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8219754 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term752 P b a _109201 _109200)). Qed.
Lemma lem8219767 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8219768 {P : Type'} (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term753 P b a _109201 _109200) = (term752 P b a _109201 _109200).
Proof. exact (@lem8219767 (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219774 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8219775 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term751 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219774 B C P p _109199 _109201) (@lem8219768 P b a _109201 _109200)). Qed.
Lemma lem8219786 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219755 B C P p _109199 b a _109201 _109200) (@lem8219775 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219787 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8219788 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term749 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219787 B C P p _109198 _109201) (@lem8219786 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219799 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219740 B C P _109198 p _109199 b a _109201 _109200) (@lem8219788 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219800 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term836 B C P z _109198 _109199 _109200 _109201) = (term836 B C P z _109198 _109199 _109200 _109201).
Proof. exact (eq_refl (term836 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219801 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term859 B C P z _109198 p _109199 b a _109201 _109200) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219800 B C P z _109198 _109199 _109200 _109201) (@lem8219799 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219812 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term858 B C P z _109198 p _109199 b a _109201 _109200) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219723 B C P z _109198 p _109199 b a _109201 _109200) (@lem8219801 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219813 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8219814 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term857 B C P h z _109198 p _109199 b a _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219813 B C P _109198 h _109199 _109201 _109200) (@lem8219812 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219825 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term856 B C P h z _109198 p _109199 b a _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219706 B C P h z _109198 p _109199 b a _109201 _109200) (@lem8219814 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219826 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term825 B C P a b p z _109198 h _109199 _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219701 B C P h z _109198 p _109199 b a _109201 _109200) (@lem8219825 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219827 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term697 B C P a b p z _109198 h _109199 _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219367 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8219826 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8219829 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term860 B C P a b p z _109198 h _109199 _109201 _109200) = (term861 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219828) (@lem8219827 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219845 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219846 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term862 B C P a b p z _109198 _109199 _109200 _109201) = (term863 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8219845 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term864 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219860 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219861 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term865 B C P a b p z _109198 _109199 _109200 _109201) = (term866 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8219860 (term615 B C P p _109198 _109201) (term622 P a _109201 _109200) (term867 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219873 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8219874 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term868 B C P a b p z _109198 _109199 _109200 _109201) = (term867 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8219873 (term622 P a _109201 _109200) (term869 B C P b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219878 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219879 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term867 B C P a b p z _109198 _109199 _109200 _109201) = (term870 B C P b a p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8219878 (term617 P _109200 b _109201) (term622 P a _109201 _109200) (term871 B C P p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219890 {B C P : Type'} (b : P -> nat) (a : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term868 B C P a b p z _109198 _109199 _109200 _109201) = (term870 B C P b a p z _109198 _109199 _109200 _109201).
Proof. exact (TRANS (@lem8219874 B C P a b p z _109198 _109199 _109200 _109201) (@lem8219879 B C P b a p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219894 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219895 {B C P : Type'} (p : type560 B C P) (a : P -> nat) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term872 B C P a p z _109198 _109199 _109200 _109201) = (term873 B C P p a z _109198 _109199 _109200 _109201).
Proof. exact (@lem8219894 (term615 B C P p _109199 _109201) (term622 P a _109201 _109200) (term602 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219909 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8219910 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term874 B C P a z _109198 _109199 _109200 _109201) = (term841 B C P z _109198 _109199 a _109201 _109200).
Proof. exact (@lem8219909 (term602 B C P z _109198 _109199 _109200 _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219918 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8219919 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term873 B C P p a z _109198 _109199 _109200 _109201) = (term842 B C P p z _109198 _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8219918 B C P p _109199 _109201) (@lem8219910 B C P z _109198 _109199 a _109201 _109200)). Qed.
Lemma lem8219923 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219924 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term842 B C P p z _109198 _109199 a _109201 _109200) = (term843 B C P z _109198 p _109199 a _109201 _109200).
Proof. exact (@lem8219923 (term602 B C P z _109198 _109199 _109200 _109201) (term615 B C P p _109199 _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219942 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term873 B C P p a z _109198 _109199 _109200 _109201) = (term843 B C P z _109198 p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8219919 B C P p z _109198 _109199 a _109201 _109200) (@lem8219924 B C P z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219943 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term872 B C P a p z _109198 _109199 _109200 _109201) = (term843 B C P z _109198 p _109199 a _109201 _109200).
Proof. exact (TRANS (@lem8219895 B C P p a z _109198 _109199 _109200 _109201) (@lem8219942 B C P z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219944 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8219945 {B C P : Type'} (b : P -> nat) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term870 B C P b a p z _109198 _109199 _109200 _109201) = (term847 B C P b z _109198 p _109199 a _109201 _109200).
Proof. exact (MK_COMB (@lem8219944 P _109200 b _109201) (@lem8219943 B C P z _109198 p _109199 a _109201 _109200)). Qed.
Lemma lem8219949 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219950 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (b : P -> nat) (p : type560 B C P) (_109199 : B -> C) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term847 B C P b z _109198 p _109199 a _109201 _109200) = (term848 B C P z _109198 b p _109199 a _109201 _109200).
Proof. exact (@lem8219949 (term602 B C P z _109198 _109199 _109200 _109201) (term617 P _109200 b _109201) (term733 B C P p _109199 a _109201 _109200)). Qed.
Lemma lem8219966 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8219967 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term734 B C P b p _109199 a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8219966 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8219983 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term836 B C P z _109198 _109199 _109200 _109201) = (term836 B C P z _109198 _109199 _109200 _109201).
Proof. exact (eq_refl (term836 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8219984 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term848 B C P z _109198 b p _109199 a _109201 _109200) = (term849 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219983 B C P z _109198 _109199 _109200 _109201) (@lem8219967 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8219995 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term847 B C P b z _109198 p _109199 a _109201 _109200) = (term849 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219950 B C P z _109198 b p _109199 a _109201 _109200) (@lem8219984 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219996 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term870 B C P b a p z _109198 _109199 _109200 _109201) = (term849 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219945 B C P b z _109198 p _109199 a _109201 _109200) (@lem8219995 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219997 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term868 B C P a b p z _109198 _109199 _109200 _109201) = (term849 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219890 B C P b a p z _109198 _109199 _109200 _109201) (@lem8219996 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8219998 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8219999 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term866 B C P a b p z _109198 _109199 _109200 _109201) = (term853 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8219998 B C P p _109198 _109201) (@lem8219997 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220003 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8220004 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term853 B C P z _109198 p _109199 b a _109201 _109200) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8220003 (term602 B C P z _109198 _109199 _109200 _109201) (term615 B C P p _109198 _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8220042 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term866 B C P a b p z _109198 _109199 _109200 _109201) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219999 B C P z _109198 p _109199 b a _109201 _109200) (@lem8220004 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220043 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term865 B C P a b p z _109198 _109199 _109200 _109201) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219861 B C P a b p z _109198 _109199 _109200 _109201) (@lem8220042 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220044 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term619 P _109200 b _109201) = (term619 P _109200 b _109201).
Proof. exact (eq_refl (term619 P _109200 b _109201)). Qed.
Lemma lem8220045 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term863 B C P a b p z _109198 _109199 _109200 _109201) = (term858 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8220044 P _109200 b _109201) (@lem8220043 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220049 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8220050 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term858 B C P z _109198 p _109199 b a _109201 _109200) = (term859 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8220049 (term602 B C P z _109198 _109199 _109200 _109201) (term617 P _109200 b _109201) (term747 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220066 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8220067 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term749 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (@lem8220066 (term615 B C P p _109198 _109201) (term617 P _109200 b _109201) (term735 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8220081 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem8220082 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term751 B C P p _109199 b a _109201 _109200).
Proof. exact (@lem8220081 (term615 B C P p _109199 _109201) (term617 P _109200 b _109201) (term752 P b a _109201 _109200)). Qed.
Lemma lem8220094 (p : Prop) (q : Prop) : (term708 p q) = (p \/ q).
Proof. exact (proj2 (@lem20669 p q)). Qed.
Lemma lem8220095 {P : Type'} (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term753 P b a _109201 _109200) = (term752 P b a _109201 _109200).
Proof. exact (@lem8220094 (term617 P _109200 b _109201) (term622 P a _109201 _109200)). Qed.
Lemma lem8220101 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term721 B C P p _109199 _109201) = (term721 B C P p _109199 _109201).
Proof. exact (eq_refl (term721 B C P p _109199 _109201)). Qed.
Lemma lem8220102 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term751 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8220101 B C P p _109199 _109201) (@lem8220095 P b a _109201 _109200)). Qed.
Lemma lem8220113 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term750 B C P p _109199 b a _109201 _109200) = (term735 B C P p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8220082 B C P p _109199 b a _109201 _109200) (@lem8220102 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8220114 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term721 B C P p _109198 _109201) = (term721 B C P p _109198 _109201).
Proof. exact (eq_refl (term721 B C P p _109198 _109201)). Qed.
Lemma lem8220115 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term749 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8220114 B C P p _109198 _109201) (@lem8220113 B C P p _109199 b a _109201 _109200)). Qed.
Lemma lem8220126 {B C P : Type'} (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term748 B C P _109198 p _109199 b a _109201 _109200) = (term747 B C P _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8220067 B C P _109198 p _109199 b a _109201 _109200) (@lem8220115 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220127 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term836 B C P z _109198 _109199 _109200 _109201) = (term836 B C P z _109198 _109199 _109200 _109201).
Proof. exact (eq_refl (term836 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220128 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term859 B C P z _109198 p _109199 b a _109201 _109200) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8220127 B C P z _109198 _109199 _109200 _109201) (@lem8220126 B C P _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220139 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term858 B C P z _109198 p _109199 b a _109201 _109200) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8220050 B C P z _109198 p _109199 b a _109201 _109200) (@lem8220128 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220140 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term863 B C P a b p z _109198 _109199 _109200 _109201) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8220045 B C P z _109198 p _109199 b a _109201 _109200) (@lem8220139 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220141 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term862 B C P a b p z _109198 _109199 _109200 _109201) = (term854 B C P z _109198 p _109199 b a _109201 _109200).
Proof. exact (TRANS (@lem8219846 B C P a b p z _109198 _109199 _109200 _109201) (@lem8220140 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220142 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term727 B C P _109198 h _109199 _109201 _109200) = (term727 B C P _109198 h _109199 _109201 _109200).
Proof. exact (eq_refl (term727 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8220143 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : (term875 B C P h a b p z _109198 _109199 _109200 _109201) = (term855 B C P h z _109198 p _109199 b a _109201 _109200).
Proof. exact (MK_COMB (@lem8220142 B C P _109198 h _109199 _109201 _109200) (@lem8220141 B C P z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220154 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : ((term697 B C P a b p z _109198 h _109199 _109201 _109200) = (term875 B C P h a b p z _109198 _109199 _109200 _109201)) = ((term855 B C P h z _109198 p _109199 b a _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200)).
Proof. exact (MK_COMB (@lem8219829 B C P h z _109198 p _109199 b a _109201 _109200) (@lem8220143 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220156 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8220157 (x : Prop) : (x = x) = True.
Proof. exact (@lem8220156 Prop x). Qed.
Lemma lem8220158 {B C P : Type'} (h : type555 B C P) (z : type521 B C P) (_109198 : B -> C) (p : type560 B C P) (_109199 : B -> C) (b : P -> nat) (a : P -> nat) (_109201 : P) (_109200 : nat) : ((term855 B C P h z _109198 p _109199 b a _109201 _109200) = (term855 B C P h z _109198 p _109199 b a _109201 _109200)) = True.
Proof. exact (@lem8220157 (term855 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220159 {B C P : Type'} (h : type555 B C P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : ((term697 B C P a b p z _109198 h _109199 _109201 _109200) = (term875 B C P h a b p z _109198 _109199 _109200 _109201)) = True.
Proof. exact (TRANS (@lem8220154 B C P h z _109198 p _109199 b a _109201 _109200) (@lem8220158 B C P h z _109198 p _109199 b a _109201 _109200)). Qed.
Lemma lem8220160 {B C P : Type'} (h : type555 B C P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : True = ((term697 B C P a b p z _109198 h _109199 _109201 _109200) = (term875 B C P h a b p z _109198 _109199 _109200 _109201)).
Proof. exact (SYM (@lem8220159 B C P h a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220161 {B C P : Type'} (h : type555 B C P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term697 B C P a b p z _109198 h _109199 _109201 _109200) = (term875 B C P h a b p z _109198 _109199 _109200 _109201).
Proof. exact (EQ_MP (@lem8220160 B C P h a b p z _109198 _109199 _109200 _109201) (@lem0)). Qed.
Lemma lem8220162 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term875 B C P h a b p z _109198 _109199 _109200 _109201.
Proof. exact (EQ_MP (@lem8220161 B C P h a b p z _109198 _109199 _109200 _109201) (@lem8217998 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1)). Qed.
Lemma lem8220164 (b : Prop) (a : Prop) : (a \/ b) = (term779 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8220165 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term875 B C P h a b p z _109198 _109199 _109200 _109201) = (term876 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (@lem8220164 (term862 B C P a b p z _109198 _109199 _109200 _109201) ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8220167 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8220168 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term877 B C P a b p z _109198 _109199 _109200 _109201) = (term878 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8220167 (term622 P a _109201 _109200) (term879 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220170 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8220171 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term786 P a _109201 _109200) = (term579 P a _109201 _109200).
Proof. exact (@lem8220170 (term579 P a _109201 _109200)). Qed.
Lemma lem8220172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220173 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term787 P a _109201 _109200) = (term581 P a _109201 _109200).
Proof. exact (MK_COMB (@lem8220172) (@lem8220171 P a _109201 _109200)). Qed.
Lemma lem8220175 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8220176 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term880 B C P a b p z _109198 _109199 _109200 _109201) = (term881 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8220175 (term617 P _109200 b _109201) (term864 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220178 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8220179 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term790 P _109200 b _109201) = (term573 P _109200 b _109201).
Proof. exact (@lem8220178 (term573 P _109200 b _109201)). Qed.
Lemma lem8220180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220181 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term791 P _109200 b _109201) = (term792 P _109200 b _109201).
Proof. exact (MK_COMB (@lem8220180) (@lem8220179 P _109200 b _109201)). Qed.
Lemma lem8220183 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8220184 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term882 B C P a b p z _109198 _109199 _109200 _109201) = (term883 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8220183 (term615 B C P p _109198 _109201) (term867 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220186 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8220187 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term795 B C P p _109198 _109201) = (term558 B C P p _109198 _109201).
Proof. exact (@lem8220186 (term558 B C P p _109198 _109201)). Qed.
Lemma lem8220188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220189 {B C P : Type'} (p : type560 B C P) (_109198 : B -> C) (_109201 : P) : (term796 B C P p _109198 _109201) = (term797 B C P p _109198 _109201).
Proof. exact (MK_COMB (@lem8220188) (@lem8220187 B C P p _109198 _109201)). Qed.
Lemma lem8220191 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8220192 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term884 B C P a b p z _109198 _109199 _109200 _109201) = (term885 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8220191 (term622 P a _109201 _109200) (term869 B C P b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220194 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8220195 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term786 P a _109201 _109200) = (term579 P a _109201 _109200).
Proof. exact (@lem8220194 (term579 P a _109201 _109200)). Qed.
Lemma lem8220196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220197 {P : Type'} (a : P -> nat) (_109201 : P) (_109200 : nat) : (term787 P a _109201 _109200) = (term581 P a _109201 _109200).
Proof. exact (MK_COMB (@lem8220196) (@lem8220195 P a _109201 _109200)). Qed.
Lemma lem8220199 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8220200 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term886 B C P b p z _109198 _109199 _109200 _109201) = (term887 B C P b p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8220199 (term617 P _109200 b _109201) (term871 B C P p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220202 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8220203 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term790 P _109200 b _109201) = (term573 P _109200 b _109201).
Proof. exact (@lem8220202 (term573 P _109200 b _109201)). Qed.
Lemma lem8220204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220205 {P : Type'} (_109200 : nat) (b : P -> nat) (_109201 : P) : (term791 P _109200 b _109201) = (term792 P _109200 b _109201).
Proof. exact (MK_COMB (@lem8220204) (@lem8220203 P _109200 b _109201)). Qed.
Lemma lem8220207 (a : Prop) (b : Prop) : (term781 a b) = (term782 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem8220208 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term888 B C P p z _109198 _109199 _109200 _109201) = (term889 B C P p z _109198 _109199 _109200 _109201).
Proof. exact (@lem8220207 (term615 B C P p _109199 _109201) (term602 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220210 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8220211 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term795 B C P p _109199 _109201) = (term558 B C P p _109199 _109201).
Proof. exact (@lem8220210 (term558 B C P p _109199 _109201)). Qed.
Lemma lem8220212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8220213 {B C P : Type'} (p : type560 B C P) (_109199 : B -> C) (_109201 : P) : (term796 B C P p _109199 _109201) = (term797 B C P p _109199 _109201).
Proof. exact (MK_COMB (@lem8220212) (@lem8220211 B C P p _109199 _109201)). Qed.
Lemma lem8220215 (a : Prop) : (term316 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8220216 {B C P : Type'} (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term890 B C P z _109198 _109199 _109200 _109201) = ((term595 B C P z _109198 _109199 _109200 _109201) = (term598 B C P z _109198 _109199 _109200 _109201)).
Proof. exact (@lem8220215 ((term595 B C P z _109198 _109199 _109200 _109201) = (term598 B C P z _109198 _109199 _109200 _109201))). Qed.
Lemma lem8220217 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term889 B C P p z _109198 _109199 _109200 _109201) = (term891 B C P p z _109198 _109199 _109200 _109201).
Proof. exact (MK_COMB (@lem8220213 B C P p _109199 _109201) (@lem8220216 B C P z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220218 {B C P : Type'} (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term888 B C P p z _109198 _109199 _109200 _109201) = (term891 B C P p z _109198 _109199 _109200 _109201).
Proof. exact (TRANS (@lem8220208 B C P p z _109198 _109199 _109200 _109201) (@lem8220217 B C P p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220219 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term887 B C P b p z _109198 _109199 _109200 _109201) = (term892 B C P b p z _109198 _109199 _109200 _109201).
Proof. exact (MK_COMB (@lem8220205 P _109200 b _109201) (@lem8220218 B C P p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220220 {B C P : Type'} (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term886 B C P b p z _109198 _109199 _109200 _109201) = (term892 B C P b p z _109198 _109199 _109200 _109201).
Proof. exact (TRANS (@lem8220200 B C P b p z _109198 _109199 _109200 _109201) (@lem8220219 B C P b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220221 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term885 B C P a b p z _109198 _109199 _109200 _109201) = (term893 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (MK_COMB (@lem8220197 P a _109201 _109200) (@lem8220220 B C P b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220222 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term884 B C P a b p z _109198 _109199 _109200 _109201) = (term893 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (TRANS (@lem8220192 B C P a b p z _109198 _109199 _109200 _109201) (@lem8220221 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220223 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term883 B C P a b p z _109198 _109199 _109200 _109201) = (term894 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (MK_COMB (@lem8220189 B C P p _109198 _109201) (@lem8220222 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220224 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term882 B C P a b p z _109198 _109199 _109200 _109201) = (term894 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (TRANS (@lem8220184 B C P a b p z _109198 _109199 _109200 _109201) (@lem8220223 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220225 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term881 B C P a b p z _109198 _109199 _109200 _109201) = (term895 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (MK_COMB (@lem8220181 P _109200 b _109201) (@lem8220224 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220226 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term880 B C P a b p z _109198 _109199 _109200 _109201) = (term895 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (TRANS (@lem8220176 B C P a b p z _109198 _109199 _109200 _109201) (@lem8220225 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220227 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term878 B C P a b p z _109198 _109199 _109200 _109201) = (term896 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (MK_COMB (@lem8220173 P a _109201 _109200) (@lem8220226 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220228 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term877 B C P a b p z _109198 _109199 _109200 _109201) = (term896 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (TRANS (@lem8220168 B C P a b p z _109198 _109199 _109200 _109201) (@lem8220227 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8220230 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (_109199 : B -> C) (_109200 : nat) (_109201 : P) : (term897 B C P a b p z _109198 _109199 _109200 _109201) = (term898 B C P a b p z _109198 _109199 _109200 _109201).
Proof. exact (MK_COMB (@lem8220229) (@lem8220228 B C P a b p z _109198 _109199 _109200 _109201)). Qed.
Lemma lem8220231 {B C P : Type'} (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)) = ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200)).
Proof. exact (eq_refl ((term585 B C P h _109198 _109201 _109200) = (term585 B C P h _109199 _109201 _109200))). Qed.
Lemma lem8220232 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term876 B C P a b p z _109198 h _109199 _109201 _109200) = (term899 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (MK_COMB (@lem8220230 B C P a b p z _109198 _109199 _109200 _109201) (@lem8220231 B C P _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8220233 {B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (z : type521 B C P) (_109198 : B -> C) (h : type555 B C P) (_109199 : B -> C) (_109201 : P) (_109200 : nat) : (term875 B C P h a b p z _109198 _109199 _109200 _109201) = (term899 B C P a b p z _109198 h _109199 _109201 _109200).
Proof. exact (TRANS (@lem8220165 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8220232 B C P a b p z _109198 h _109199 _109201 _109200)). Qed.
Lemma lem8220235 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term891 B C P p z f g i a'.
Proof. exact (conj (@lem8218334 B C P p g a' h6) (@lem8219360 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220236 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term892 B C P b p z f g i a'.
Proof. exact (conj (@lem8218327 P a i b a' h4) (@lem8220235 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220237 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term893 B C P a b p z f g i a'.
Proof. exact (conj (@lem8218320 P a i b a' h4) (@lem8220236 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220238 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term894 B C P a b p z f g i a'.
Proof. exact (conj (@lem8218313 B C P p f a' h5) (@lem8220237 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220239 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term895 B C P a b p z f g i a'.
Proof. exact (conj (@lem8218306 P a i b a' h4) (@lem8220238 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220240 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term896 B C P a b p z f g i a'.
Proof. exact (conj (@lem8218299 P a i b a' h4) (@lem8220239 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220242 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term899 B C P a b p z _109198 h _109199 _109201 _109200.
Proof. exact (EQ_MP (@lem8220233 B C P a b p z _109198 h _109199 _109201 _109200) (@lem8220162 A B C P _109198 _109199 _109200 _109201 a b p lt2 s z h h1)). Qed.
Lemma lem8220243 {A B C P : Type'} (_109198 : B -> C) (_109199 : B -> C) (_109201 : P) (_109200 : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term899 B C P a b p z _109198 h _109199 _109201 _109200.
Proof. exact (@lem8220242 A B C P _109198 _109199 _109201 _109200 a b p lt2 s z h h1). Qed.
Lemma lem8220244 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (i : nat) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (h1 : term550 A B C P a b p lt2 s z h) : term899 B C P a b p z f h g a' i.
Proof. exact (@lem8220243 A B C P f g a' i a b p lt2 s z h h1). Qed.
Lemma lem8220247 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term587 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term585 B C P h f a' i) = (term585 B C P h g a' i).
Proof. exact (@lem8220244 A B C P f g a' i a b p lt2 s z h h2 (@lem8220240 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220248 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term900 B C P f h g a' i.
Proof. exact (fun h0 : term587 B C P f h g a' i => @lem8220247 A B C P lt2 s z h a i b f p g a' h1 h2 h0 h3 h4 h5). Qed.
Lemma lem8220250 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8220251 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (term900 B C P f h g a' i) = ((term585 B C P h f a' i) = (term585 B C P h g a' i)).
Proof. exact (@lem8220250 ((term585 B C P h f a' i) = (term585 B C P h g a' i))). Qed.
Lemma lem8220252 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : (term585 B C P h f a' i) = (term585 B C P h g a' i).
Proof. exact (EQ_MP (@lem8220251 B C P f h g a' i) (@lem8220248 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5)). Qed.
Lemma lem8220255 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8220257 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) : (term587 B C P f h g a' i) = (term901 B C P f h g a' i).
Proof. exact (@lem8220255 ((term585 B C P h f a' i) = (term585 B C P h g a' i))). Qed.
Lemma lem8220260 {B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (i : nat) (h1 : term365 B C P f h g a' i) : term901 B C P f h g a' i.
Proof. exact (EQ_MP (@lem8220257 B C P f h g a' i) (@lem8217910 B C P f h g a' i h1)). Qed.
Lemma lem8220263 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (@lem8220260 B C P f h g a' i h3 (@lem8220252 A B C P lt2 s z h a i b f p g a' h1 h2 h4 h5 h6)). Qed.
Lemma lem8220264 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : term902.
Proof. exact (fun h0 : ~ False => @lem8220263 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6). Qed.
Lemma lem8220266 (p : Prop) : (term699 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8220267 : term902 = False.
Proof. exact (@lem8220266 False). Qed.
Lemma lem8220268 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (z : type521 B C P) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term550 A B C P a b p lt2 s z h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8220267) (@lem8220264 A B C P lt2 s z h a i b f p g a' h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem8220269 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (ex_elim (@lem8217095 A B C P a b p lt2 s h h2) (fun z : type521 B C P => fun h0 : term552 A B C P a b p lt2 s h z => @lem8220268 A B C P lt2 s z h a i b f p g a' h1 h0 h3 h4 h5 h6)). Qed.
Lemma lem8220270 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term365 B C P f h g a' i) = False.
Proof. exact (prop_ext (fun h7 : term365 B C P f h g a' i => @lem8220269 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8217186 B C P f h g a' i h3)). Qed.
Lemma lem8220271 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8220270 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8217186 B C P f h g a' i h3)). Qed.
Lemma lem8220272 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term557 P a i b a') = False.
Proof. exact (prop_ext (fun h7 : term557 P a i b a' => @lem8220271 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8217180 P a i b a' h4)). Qed.
Lemma lem8220273 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8220272 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8217180 P a i b a' h4)). Qed.
Lemma lem8220274 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (p g a') = False.
Proof. exact (prop_ext (fun h7 : p g a' => @lem8220273 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8217107 B C P p g a' h6)). Qed.
Lemma lem8220275 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8220274 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8217107 B C P p g a' h6)). Qed.
Lemma lem8220276 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (p f a') = False.
Proof. exact (prop_ext (fun h7 : p f a' => @lem8220275 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8217101 B C P p f a' h5)). Qed.
Lemma lem8220277 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8220276 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8217101 B C P p f a' h5)). Qed.
Lemma lem8220278 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : (term365 B C P f h g a' i) = False.
Proof. exact (prop_ext (fun h7 : term365 B C P f h g a' i => @lem8220277 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem8216704 B C P f h g a' i h3)). Qed.
Lemma lem8220279 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term365 B C P f h g a' i) (h4 : term557 P a i b a') (h5 : p f a') (h6 : p g a') : False.
Proof. exact (EQ_MP (@lem8220278 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5 h6) (@lem8216704 B C P f h g a' i h3)). Qed.
Lemma lem8220280 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : term364 B C P f h g a' i.
Proof. exact (fun h0 : term365 B C P f h g a' i => @lem8220279 A B C P lt2 s h a i b f p g a' h1 h2 h0 h3 h4 h5). Qed.
Lemma lem8220281 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (a : P -> nat) (i : nat) (b : P -> nat) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term557 P a i b a') (h4 : p f a') (h5 : p g a') : (h f a' i) = (h g a' i).
Proof. exact (EQ_MP (@lem8216703 B C P f h g a' i) (@lem8220280 A B C P lt2 s h a i b f p g a' h1 h2 h3 h4 h5)). Qed.
Lemma lem8220282 {A B C P : Type'} (i : nat) (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term362 B C P a b f h g a' i.
Proof. exact (fun h0 : term557 P a i b a' => @lem8220281 A B C P lt2 s h a i b f p g a' h1 h2 h0 h3 h4). Qed.
Lemma lem8220287 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term308 B C P a b f h g a'.
Proof. exact (fun i : nat => @lem8220282 A B C P i a b lt2 s h f p g a' h1 h2 h3 h4). Qed.
Lemma lem8220288 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') (h3 : p g a') : term319 A B C P lt2 s a b f h g a'.
Proof. exact (fun h0 : term174 A B C P lt2 s a' f g => @lem8220287 A B C P a b lt2 s h f p g a' h0 h1 h2 h3). Qed.
Lemma lem8220289 {A B C P : Type'} (g : B -> C) (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') : term322 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : p g a' => @lem8220288 A B C P a b lt2 s h f p g a' h1 h2 h0). Qed.
Lemma lem8220290 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term324 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : p f a' => @lem8220289 A B C P g a b lt2 s h p f a' h1 h0). Qed.
Lemma lem8220291 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term325 A B C P p lt2 s a b f h g a'.
Proof. exact (fun h0 : term240 A B C P a b p lt2 s h => @lem8220290 A B C P f g a' a b p lt2 s h h0). Qed.
Lemma lem8220296 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term329 A B C P lt2 s a b f h g a'.
Proof. exact (fun p : type560 B C P => @lem8220291 A B C P p lt2 s a b f h g a'). Qed.
Lemma lem8220301 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term333 A B C P s a b f h g a'.
Proof. exact (fun lt2 : type1470 A B => @lem8220296 A B C P lt2 s a b f h g a'). Qed.
Lemma lem8220306 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term337 A B C P a b f h g a'.
Proof. exact (fun s : P -> A => @lem8220301 A B C P s a b f h g a'). Qed.
Lemma lem8220311 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term341 A B C P b f h g a'.
Proof. exact (fun a : P -> nat => @lem8220306 A B C P a b f h g a'). Qed.
Lemma lem8220316 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term345 A B C P f h g a'.
Proof. exact (fun b : P -> nat => @lem8220311 A B C P b f h g a'). Qed.
Lemma lem8220321 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : term349 A B C P h g a'.
Proof. exact (fun f : B -> C => @lem8220316 A B C P f h g a'). Qed.
Lemma lem8220326 {A B C P : Type'} (g : B -> C) (a' : P) : term353 A B C P g a'.
Proof. exact (fun h : type555 B C P => @lem8220321 A B C P h g a'). Qed.
Lemma lem8220331 {A B C P : Type'} (a' : P) : term357 A B C P a'.
Proof. exact (fun g : B -> C => @lem8220326 A B C P g a'). Qed.
Lemma lem8220336 {A B C P : Type'} : term361 A B C P.
Proof. exact (fun a' : P => @lem8220331 A B C P a'). Qed.
Lemma lem8220337 {A B C P : Type'} : term360 A B C P.
Proof. exact (EQ_MP (@lem8216694 A B C P) (@lem8220336 A B C P)). Qed.
Lemma lem8220338 {A B C P : Type'} (a' : P) : term903 A B C P a'.
Proof. exact (@lem8220337 A B C P a'). Qed.
Lemma lem8220339 {A B C P : Type'} (a' : P) : (term903 A B C P a') = (term356 A B C P a').
Proof. exact (eq_refl (term903 A B C P a')). Qed.
Lemma lem8220340 {A B C P : Type'} (a' : P) : term356 A B C P a'.
Proof. exact (EQ_MP (@lem8220339 A B C P a') (@lem8220338 A B C P a')). Qed.
Lemma lem8220341 {A B C P : Type'} (a' : P) (g : B -> C) : term904 A B C P a' g.
Proof. exact (@lem8220340 A B C P a' g). Qed.
Lemma lem8220342 {A B C P : Type'} (g : B -> C) (a' : P) : (term904 A B C P a' g) = (term352 A B C P g a').
Proof. exact (eq_refl (term904 A B C P a' g)). Qed.
Lemma lem8220343 {A B C P : Type'} (g : B -> C) (a' : P) : term352 A B C P g a'.
Proof. exact (EQ_MP (@lem8220342 A B C P g a') (@lem8220341 A B C P a' g)). Qed.
Lemma lem8220344 {A B C P : Type'} (g : B -> C) (a' : P) (h : type555 B C P) : term905 A B C P g a' h.
Proof. exact (@lem8220343 A B C P g a' h). Qed.
Lemma lem8220345 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : (term905 A B C P g a' h) = (term348 A B C P h g a').
Proof. exact (eq_refl (term905 A B C P g a' h)). Qed.
Lemma lem8220346 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) : term348 A B C P h g a'.
Proof. exact (EQ_MP (@lem8220345 A B C P h g a') (@lem8220344 A B C P g a' h)). Qed.
Lemma lem8220347 {A B C P : Type'} (h : type555 B C P) (g : B -> C) (a' : P) (f : B -> C) : term906 A B C P h g a' f.
Proof. exact (@lem8220346 A B C P h g a' f). Qed.
Lemma lem8220348 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term906 A B C P h g a' f) = (term344 A B C P f h g a').
Proof. exact (eq_refl (term906 A B C P h g a' f)). Qed.
Lemma lem8220349 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term344 A B C P f h g a'.
Proof. exact (EQ_MP (@lem8220348 A B C P f h g a') (@lem8220347 A B C P h g a' f)). Qed.
Lemma lem8220350 {A B C P : Type'} (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (b : P -> nat) : term907 A B C P f h g a' b.
Proof. exact (@lem8220349 A B C P f h g a' b). Qed.
Lemma lem8220351 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term907 A B C P f h g a' b) = (term340 A B C P b f h g a').
Proof. exact (eq_refl (term907 A B C P f h g a' b)). Qed.
Lemma lem8220352 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term340 A B C P b f h g a'.
Proof. exact (EQ_MP (@lem8220351 A B C P b f h g a') (@lem8220350 A B C P f h g a' b)). Qed.
Lemma lem8220353 {A B C P : Type'} (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (a : P -> nat) : term908 A B C P b f h g a' a.
Proof. exact (@lem8220352 A B C P b f h g a' a). Qed.
Lemma lem8220354 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term908 A B C P b f h g a' a) = (term336 A B C P a b f h g a').
Proof. exact (eq_refl (term908 A B C P b f h g a' a)). Qed.
Lemma lem8220355 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term336 A B C P a b f h g a'.
Proof. exact (EQ_MP (@lem8220354 A B C P a b f h g a') (@lem8220353 A B C P b f h g a' a)). Qed.
Lemma lem8220356 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (s : P -> A) : term909 A B C P a b f h g a' s.
Proof. exact (@lem8220355 A B C P a b f h g a' s). Qed.
Lemma lem8220357 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term909 A B C P a b f h g a' s) = (term332 A B C P s a b f h g a').
Proof. exact (eq_refl (term909 A B C P a b f h g a' s)). Qed.
Lemma lem8220358 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term332 A B C P s a b f h g a'.
Proof. exact (EQ_MP (@lem8220357 A B C P s a b f h g a') (@lem8220356 A B C P a b f h g a' s)). Qed.
Lemma lem8220359 {A B C P : Type'} (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (lt2 : type1470 A B) : term910 A B C P s a b f h g a' lt2.
Proof. exact (@lem8220358 A B C P s a b f h g a' lt2). Qed.
Lemma lem8220360 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term910 A B C P s a b f h g a' lt2) = (term328 A B C P lt2 s a b f h g a').
Proof. exact (eq_refl (term910 A B C P s a b f h g a' lt2)). Qed.
Lemma lem8220361 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term328 A B C P lt2 s a b f h g a'.
Proof. exact (EQ_MP (@lem8220360 A B C P lt2 s a b f h g a') (@lem8220359 A B C P s a b f h g a' lt2)). Qed.
Lemma lem8220362 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) (p : type560 B C P) : term911 A B C P lt2 s a b f h g a' p.
Proof. exact (@lem8220361 A B C P lt2 s a b f h g a' p). Qed.
Lemma lem8220363 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : (term911 A B C P lt2 s a b f h g a' p) = (term311 A B C P p lt2 s a b f h g a').
Proof. exact (eq_refl (term911 A B C P lt2 s a b f h g a' p)). Qed.
Lemma lem8220364 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (EQ_MP (@lem8220363 A B C P p lt2 s a b f h g a') (@lem8220362 A B C P lt2 s a b f h g a' p)). Qed.
Lemma lem8220366 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (f : B -> C) (h : type555 B C P) (g : B -> C) (a' : P) : term311 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8216271 A B C P p lt2 s a b f h g a' (@lem8220364 A B C P p lt2 s a b f h g a')). Qed.
Lemma lem8220367 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term323 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8220366 A B C P p lt2 s a b f h g a' (@lem8216242 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8220368 {A B C P : Type'} (g : B -> C) (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') : term321 A B C P p lt2 s a b f h g a'.
Proof. exact (@lem8220367 A B C P f g a' a b p lt2 s h h1 (@lem8216245 B C P p f a' h2)). Qed.
Lemma lem8220369 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : p f a') (h3 : p g a') : term318 A B C P lt2 s a b f h g a'.
Proof. exact (@lem8220368 A B C P g a b lt2 s h p f a' h1 h2 (@lem8216247 B C P p g a' h3)). Qed.
Lemma lem8220370 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term309 B C P a b f h g a'.
Proof. exact (@lem8220369 A B C P a b lt2 s h f p g a' h2 h3 h4 (@lem8216246 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8220371 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term310 B C P a b f h g a') (h4 : p f a') (h5 : p g a') : False.
Proof. exact (@lem8220370 A B C P a b lt2 s h f p g a' h1 h2 h4 h5 (@lem8216255 B C P a b f h g a' h3)). Qed.
Lemma lem8220372 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term310 B C P a b f h g a') (h4 : p f a') (h5 : p g a') : (term310 B C P a b f h g a') = False.
Proof. exact (prop_ext (fun h6 : term310 B C P a b f h g a' => @lem8220371 A B C P lt2 s a b h f p g a' h1 h2 h3 h4 h5) (fun h6 : False => @lem8216255 B C P a b f h g a' h3)). Qed.
Lemma lem8220373 {A B C P : Type'} (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : term310 B C P a b f h g a') (h4 : p f a') (h5 : p g a') : False.
Proof. exact (EQ_MP (@lem8220372 A B C P lt2 s a b h f p g a' h1 h2 h3 h4 h5) (@lem8216255 B C P a b f h g a' h3)). Qed.
Lemma lem8220374 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term309 B C P a b f h g a'.
Proof. exact (fun h0 : term310 B C P a b f h g a' => @lem8220373 A B C P lt2 s a b h f p g a' h1 h2 h0 h3 h4). Qed.
Lemma lem8220375 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : term308 B C P a b f h g a'.
Proof. exact (EQ_MP (@lem8216254 B C P a b f h g a') (@lem8220374 A B C P a b lt2 s h f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8220376 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (@lem8216250 B C P f a b h g a' (@lem8220375 A B C P a b lt2 s h f p g a' h1 h2 h3 h4)). Qed.
Lemma lem8220377 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term304 A B C P p lt2 s a' f g) : term305 A B C P p lt2 s a' f g.
Proof. exact (proj2 (@lem8216243 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8220378 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term304 A B C P p lt2 s a' f g) : p f a'.
Proof. exact (proj1 (@lem8216243 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8220379 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term305 A B C P p lt2 s a' f g) : term174 A B C P lt2 s a' f g.
Proof. exact (proj2 (@lem8216244 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8220380 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term305 A B C P p lt2 s a' f g) : p g a'.
Proof. exact (proj1 (@lem8216244 A B C P p lt2 s a' f g h1)). Qed.
Lemma lem8220381 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term174 A B C P lt2 s a' f g) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h5 : term174 A B C P lt2 s a' f g => @lem8220376 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (fun h5 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8216246 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8220382 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8220381 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (@lem8216246 A B C P lt2 s a' f g h1)). Qed.
Lemma lem8220383 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (p g a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h5 : p g a' => @lem8220382 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (fun h5 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8216247 B C P p g a' h4)). Qed.
Lemma lem8220384 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term174 A B C P lt2 s a' f g) (h2 : term240 A B C P a b p lt2 s h) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8220383 A B C P a b lt2 s h f p g a' h1 h2 h3 h4) (@lem8216247 B C P p g a' h4)). Qed.
Lemma lem8220385 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') (h4 : p g a') : (term174 A B C P lt2 s a' f g) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h5 : term174 A B C P lt2 s a' f g => @lem8220384 A B C P a b lt2 s h f p g a' h5 h1 h3 h4) (fun h5 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8220379 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220386 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (f : B -> C) (p : type560 B C P) (g : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') (h4 : p g a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8220385 A B C P a b h lt2 s f p g a' h1 h2 h3 h4) (@lem8220379 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220387 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (p g a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h4 : p g a' => @lem8220386 A B C P a b h lt2 s f p g a' h1 h2 h3 h4) (fun h4 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8220380 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220388 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8220387 A B C P a b h lt2 s g p f a' h1 h2 h3) (@lem8220380 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220389 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (p f a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h4 : p f a' => @lem8220388 A B C P a b h lt2 s g p f a' h1 h2 h3) (fun h4 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8216245 B C P p f a' h3)). Qed.
Lemma lem8220390 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term305 A B C P p lt2 s a' f g) (h3 : p f a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8220389 A B C P a b h lt2 s g p f a' h1 h2 h3) (@lem8216245 B C P p f a' h3)). Qed.
Lemma lem8220391 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) (h3 : p f a') : (term305 A B C P p lt2 s a' f g) = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h4 : term305 A B C P p lt2 s a' f g => @lem8220390 A B C P a b h lt2 s g p f a' h1 h4 h3) (fun h4 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8220377 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220392 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (lt2 : type1470 A B) (s : P -> A) (g : B -> C) (p : type560 B C P) (f : B -> C) (a' : P) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) (h3 : p f a') : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8220391 A B C P a b h lt2 s g p f a' h1 h2 h3) (@lem8220377 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220393 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) : (p f a') = ((term258 B C P a b h f a') = (term258 B C P a b h g a')).
Proof. exact (prop_ext (fun h3 : p f a' => @lem8220392 A B C P a b h lt2 s g p f a' h1 h2 h3) (fun h3 : (term258 B C P a b h f a') = (term258 B C P a b h g a') => @lem8220378 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220394 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (h : type555 B C P) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a' : P) (f : B -> C) (g : B -> C) (h1 : term240 A B C P a b p lt2 s h) (h2 : term304 A B C P p lt2 s a' f g) : (term258 B C P a b h f a') = (term258 B C P a b h g a').
Proof. exact (EQ_MP (@lem8220393 A B C P a b h p lt2 s a' f g h1 h2) (@lem8220378 A B C P p lt2 s a' f g h2)). Qed.
Lemma lem8220395 {A B C P : Type'} (f : B -> C) (g : B -> C) (a' : P) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term266 A B C P p lt2 s f a b h g a'.
Proof. exact (fun h0 : term304 A B C P p lt2 s a' f g => @lem8220394 A B C P a b h p lt2 s a' f g h1 h0). Qed.
Lemma lem8220400 {A B C P : Type'} (f : B -> C) (g : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term270 A B C P p lt2 s f a b h g.
Proof. exact (fun a' : P => @lem8220395 A B C P f g a' a b p lt2 s h h1). Qed.
Lemma lem8220405 {A B C P : Type'} (f : B -> C) (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term274 A B C P p lt2 s f a b h.
Proof. exact (fun g : B -> C => @lem8220400 A B C P f g a b p lt2 s h h1). Qed.
Lemma lem8220410 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term277 A B C P p lt2 s a b h.
Proof. exact (fun f : B -> C => @lem8220405 A B C P f a b p lt2 s h h1). Qed.
Lemma lem8220411 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : (term240 A B C P a b p lt2 s h) = (term277 A B C P p lt2 s a b h).
Proof. exact (prop_ext (fun h2 : term240 A B C P a b p lt2 s h => @lem8220410 A B C P a b p lt2 s h h1) (fun h2 : term277 A B C P p lt2 s a b h => @lem8216242 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8220412 {A B C P : Type'} (a : P -> nat) (b : P -> nat) (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) (h1 : term240 A B C P a b p lt2 s h) : term277 A B C P p lt2 s a b h.
Proof. exact (EQ_MP (@lem8220411 A B C P a b p lt2 s h h1) (@lem8216242 A B C P a b p lt2 s h h1)). Qed.
Lemma lem8220413 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (b : P -> nat) (h : type555 B C P) : term279 A B C P p lt2 s a b h.
Proof. exact (fun h0 : term240 A B C P a b p lt2 s h => @lem8220412 A B C P a b p lt2 s h h0). Qed.
Lemma lem8220418 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (a : P -> nat) (h : type555 B C P) : term283 A B C P p lt2 s a h.
Proof. exact (fun b : P -> nat => @lem8220413 A B C P p lt2 s a b h). Qed.
Lemma lem8220423 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) (h : type555 B C P) : term287 A B C P p lt2 s h.
Proof. exact (fun a : P -> nat => @lem8220418 A B C P p lt2 s a h). Qed.
Lemma lem8220428 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) (s : P -> A) : term291 A B C P p lt2 s.
Proof. exact (fun h : type555 B C P => @lem8220423 A B C P p lt2 s h). Qed.
Lemma lem8220433 {A B C P : Type'} (p : type560 B C P) (lt2 : type1470 A B) : term295 A B C P p lt2.
Proof. exact (fun s : P -> A => @lem8220428 A B C P p lt2 s). Qed.
Lemma lem8220438 {A B C P : Type'} (lt2 : type1470 A B) : term299 A B C P lt2.
Proof. exact (fun p : type560 B C P => @lem8220433 A B C P p lt2). Qed.
Lemma lem8220443 {A B C P : Type'} : term303 A B C P.
Proof. exact (fun lt2 : type1470 A B => @lem8220438 A B C P lt2). Qed.
Lemma lem8220444 {A B C P : Type'} : term302 A B C P.
Proof. exact (EQ_MP (@lem8216241 A B C P) (@lem8220443 A B C P)). Qed.
