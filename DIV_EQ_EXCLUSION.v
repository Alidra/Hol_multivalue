Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_EQ_EXCLUSION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import DIV_LE_EXCLUSION_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_ANTISYM_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1822_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm89994_spec.
Lemma lem216055 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem216056 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem216057 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem216056 t1) (@lem216055 t1)). Qed.
Lemma lem216058 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem216057 t1 t2). Qed.
Lemma lem216059 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem216060 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem216059 t1 t2) (@lem216058 t1 t2)). Qed.
Lemma lem216061 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem216060 t1 t2 t3). Qed.
Lemma lem216062 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem216063 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem216062 t1 t2 t3) (@lem216061 t1 t2 t3)). Qed.
Lemma lem216064 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem216063 t1 t2 t3)). Qed.
Lemma lem216065 (d : nat) : term7 d.
Proof. exact (@lem9784 (d = (NUMERAL 0))). Qed.
Lemma lem216066 (d : nat) : (term7 d) = (term8 d).
Proof. exact (eq_refl (term7 d)). Qed.
Lemma lem216067 (d : nat) : term8 d.
Proof. exact (EQ_MP (@lem216066 d) (@lem216065 d)). Qed.
Lemma lem216069 (d : nat) (h1 : term9 d) : term9 d.
Proof. exact (h1). Qed.
Lemma lem216070 (b : nat) : term7 b.
Proof. exact (@lem9784 (b = (NUMERAL 0))). Qed.
Lemma lem216071 (b : nat) : (term7 b) = (term8 b).
Proof. exact (eq_refl (term7 b)). Qed.
Lemma lem216072 (b : nat) : term8 b.
Proof. exact (EQ_MP (@lem216071 b) (@lem216070 b)). Qed.
Lemma lem216074 (b : nat) (h1 : term9 b) : term9 b.
Proof. exact (h1). Qed.
Lemma lem216082 : term10.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem216083 (m : nat) : term11 m.
Proof. exact (@lem216082 m). Qed.
Lemma lem216084 (m : nat) : (term11 m) = ((term12 m) = False).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem216086 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem216112 : term14.
Proof. exact (proj1 (@lem216086)). Qed.
Lemma lem216113 (m : nat) : term15 m.
Proof. exact (@lem216112 m). Qed.
Lemma lem216114 (m : nat) : (term15 m) = ((term16 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem216116 : term17.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem216117 (n : nat) : term18 n.
Proof. exact (@lem216116 n). Qed.
Lemma lem216118 (n : nat) : (term18 n) = ((term19 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem216125 (b : nat) (h1 : b = (NUMERAL 0)) : b = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem216126 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem216127 (b : nat) (h1 : b = (NUMERAL 0)) : (Nat.mul b) = term20.
Proof. exact (MK_COMB (@lem216126) (@lem216125 b h1)). Qed.
Lemma lem216128 (c : nat) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem216129 (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (Nat.mul b c) = (term19 c).
Proof. exact (MK_COMB (@lem216127 b h1) (@lem216128 c)). Qed.
Lemma lem216131 (n : nat) : (term19 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem216118 n) (@lem216117 n)). Qed.
Lemma lem216132 (c : nat) : (term19 c) = (NUMERAL 0).
Proof. exact (@lem216131 c). Qed.
Lemma lem216133 (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (Nat.mul b c) = (NUMERAL 0).
Proof. exact (TRANS (@lem216129 c b h1) (@lem216132 c)). Qed.
Lemma lem216134 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem216135 (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term21 b c) = term22.
Proof. exact (MK_COMB (@lem216134) (@lem216133 c b h1)). Qed.
Lemma lem216136 (a : nat) (d : nat) : (term23 a d) = (term23 a d).
Proof. exact (eq_refl (term23 a d)). Qed.
Lemma lem216137 (c : nat) (a : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term24 b c a d) = (term25 a d).
Proof. exact (MK_COMB (@lem216135 c b h1) (@lem216136 a d)). Qed.
Lemma lem216138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem216139 (c : nat) (a : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term26 b c a d) = (term27 a d).
Proof. exact (MK_COMB (@lem216138) (@lem216137 c a d b h1)). Qed.
Lemma lem216141 (b : nat) (h1 : b = (NUMERAL 0)) : b = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem216142 (c : nat) : (term28 c) = (term28 c).
Proof. exact (eq_refl (term28 c)). Qed.
Lemma lem216143 (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term23 c b) = (term29 c).
Proof. exact (MK_COMB (@lem216142 c) (@lem216141 b h1)). Qed.
Lemma lem216145 (m : nat) : (term16 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem216114 m) (@lem216113 m)). Qed.
Lemma lem216146 (c : nat) : (term29 c) = (NUMERAL 0).
Proof. exact (@lem216145 (term30 c)). Qed.
Lemma lem216147 (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term23 c b) = (NUMERAL 0).
Proof. exact (TRANS (@lem216143 c b h1) (@lem216146 c)). Qed.
Lemma lem216148 (a : nat) (d : nat) : (term21 a d) = (term21 a d).
Proof. exact (eq_refl (term21 a d)). Qed.
Lemma lem216149 (c : nat) (a : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term24 a d c b) = (term31 a d).
Proof. exact (MK_COMB (@lem216148 a d) (@lem216147 c b h1)). Qed.
Lemma lem216151 (m : nat) : (term12 m) = False.
Proof. exact (EQ_MP (@lem216084 m) (@lem216083 m)). Qed.
Lemma lem216152 (a : nat) (d : nat) : (term31 a d) = False.
Proof. exact (@lem216151 (Nat.mul a d)). Qed.
Lemma lem216153 (a : nat) (d : nat) (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term24 a d c b) = False.
Proof. exact (TRANS (@lem216149 c a d b h1) (@lem216152 a d)). Qed.
Lemma lem216154 (c : nat) (a : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term32 a d c b) = (term33 a d).
Proof. exact (MK_COMB (@lem216139 c a d b h1) (@lem216153 a d c b h1)). Qed.
Lemma lem216156 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem216157 (a : nat) (d : nat) : (term33 a d) = False.
Proof. exact (@lem216156 (term25 a d)). Qed.
Lemma lem216158 (a : nat) (d : nat) (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term32 a d c b) = False.
Proof. exact (TRANS (@lem216154 c a d b h1) (@lem216157 a d)). Qed.
Lemma lem216159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem216160 (a : nat) (d : nat) (c : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term34 a d c b) = (imp False).
Proof. exact (MK_COMB (@lem216159) (@lem216158 a d c b h1)). Qed.
Lemma lem216164 (b : nat) (h1 : b = (NUMERAL 0)) : b = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem216165 (a : nat) : (Nat.div a) = (Nat.div a).
Proof. exact (eq_refl (Nat.div a)). Qed.
Lemma lem216166 (a : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (Nat.div a b) = (term35 a).
Proof. exact (MK_COMB (@lem216165 a) (@lem216164 b h1)). Qed.
Lemma lem216167 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem216168 (a : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term36 a b) = (term37 a).
Proof. exact (MK_COMB (@lem216167) (@lem216166 a b h1)). Qed.
Lemma lem216169 (c : nat) (d : nat) : (Nat.div c d) = (Nat.div c d).
Proof. exact (eq_refl (Nat.div c d)). Qed.
Lemma lem216170 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : ((Nat.div a b) = (Nat.div c d)) = ((term35 a) = (Nat.div c d)).
Proof. exact (MK_COMB (@lem216168 a b h1) (@lem216169 c d)). Qed.
Lemma lem216173 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term38 a b c d) = (term39 a c d).
Proof. exact (MK_COMB (@lem216160 a d c b h1) (@lem216170 a c d b h1)). Qed.
Lemma lem216175 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem216176 (a : nat) (c : nat) (d : nat) : (term39 a c d) = True.
Proof. exact (@lem216175 ((term35 a) = (Nat.div c d))). Qed.
Lemma lem216177 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : (term38 a b c d) = True.
Proof. exact (TRANS (@lem216173 a c d b h1) (@lem216176 a c d)). Qed.
Lemma lem216178 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : True = (term38 a b c d).
Proof. exact (SYM (@lem216177 a c d b h1)). Qed.
Lemma lem216179 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : b = (NUMERAL 0)) : term38 a b c d.
Proof. exact (EQ_MP (@lem216178 a c d b h1) (@lem0)). Qed.
Lemma lem216253 : term10.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem216254 (m : nat) : term11 m.
Proof. exact (@lem216253 m). Qed.
Lemma lem216255 (m : nat) : (term11 m) = ((term12 m) = False).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem216257 : term13.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem216283 : term14.
Proof. exact (proj1 (@lem216257)). Qed.
Lemma lem216284 (m : nat) : term15 m.
Proof. exact (@lem216283 m). Qed.
Lemma lem216285 (m : nat) : (term15 m) = ((term16 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem216309 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem216310 (a : nat) : (term28 a) = (term28 a).
Proof. exact (eq_refl (term28 a)). Qed.
Lemma lem216311 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term23 a d) = (term29 a).
Proof. exact (MK_COMB (@lem216310 a) (@lem216309 d h1)). Qed.
Lemma lem216313 (m : nat) : (term16 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem216285 m) (@lem216284 m)). Qed.
Lemma lem216314 (a : nat) : (term29 a) = (NUMERAL 0).
Proof. exact (@lem216313 (term30 a)). Qed.
Lemma lem216315 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term23 a d) = (NUMERAL 0).
Proof. exact (TRANS (@lem216311 a d h1) (@lem216314 a)). Qed.
Lemma lem216316 (b : nat) (c : nat) : (term21 b c) = (term21 b c).
Proof. exact (eq_refl (term21 b c)). Qed.
Lemma lem216317 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term24 b c a d) = (term31 b c).
Proof. exact (MK_COMB (@lem216316 b c) (@lem216315 a d h1)). Qed.
Lemma lem216319 (m : nat) : (term12 m) = False.
Proof. exact (EQ_MP (@lem216255 m) (@lem216254 m)). Qed.
Lemma lem216320 (b : nat) (c : nat) : (term31 b c) = False.
Proof. exact (@lem216319 (Nat.mul b c)). Qed.
Lemma lem216321 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term24 b c a d) = False.
Proof. exact (TRANS (@lem216317 a b c d h1) (@lem216320 b c)). Qed.
Lemma lem216322 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem216323 (b : nat) (c : nat) (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term26 b c a d) = (and False).
Proof. exact (MK_COMB (@lem216322) (@lem216321 b c a d h1)). Qed.
Lemma lem216325 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem216326 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem216327 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.mul a d) = (term16 a).
Proof. exact (MK_COMB (@lem216326 a) (@lem216325 d h1)). Qed.
Lemma lem216329 (m : nat) : (term16 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem216285 m) (@lem216284 m)). Qed.
Lemma lem216330 (a : nat) : (term16 a) = (NUMERAL 0).
Proof. exact (@lem216329 a). Qed.
Lemma lem216331 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.mul a d) = (NUMERAL 0).
Proof. exact (TRANS (@lem216327 a d h1) (@lem216330 a)). Qed.
Lemma lem216332 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem216333 (a : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term21 a d) = term22.
Proof. exact (MK_COMB (@lem216332) (@lem216331 a d h1)). Qed.
Lemma lem216334 (c : nat) (b : nat) : (term23 c b) = (term23 c b).
Proof. exact (eq_refl (term23 c b)). Qed.
Lemma lem216335 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term24 a d c b) = (term25 c b).
Proof. exact (MK_COMB (@lem216333 a d h1) (@lem216334 c b)). Qed.
Lemma lem216336 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term32 a d c b) = (term40 c b).
Proof. exact (MK_COMB (@lem216323 b c a d h1) (@lem216335 a c b d h1)). Qed.
Lemma lem216338 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem216339 (c : nat) (b : nat) : (term40 c b) = False.
Proof. exact (@lem216338 (term25 c b)). Qed.
Lemma lem216340 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term32 a d c b) = False.
Proof. exact (TRANS (@lem216336 a c b d h1) (@lem216339 c b)). Qed.
Lemma lem216341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem216342 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term34 a d c b) = (imp False).
Proof. exact (MK_COMB (@lem216341) (@lem216340 a c b d h1)). Qed.
Lemma lem216346 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem216347 (c : nat) : (Nat.div c) = (Nat.div c).
Proof. exact (eq_refl (Nat.div c)). Qed.
Lemma lem216348 (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (Nat.div c d) = (term35 c).
Proof. exact (MK_COMB (@lem216347 c) (@lem216346 d h1)). Qed.
Lemma lem216349 (a : nat) (b : nat) : (term36 a b) = (term36 a b).
Proof. exact (eq_refl (term36 a b)). Qed.
Lemma lem216350 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : ((Nat.div a b) = (Nat.div c d)) = ((Nat.div a b) = (term35 c)).
Proof. exact (MK_COMB (@lem216349 a b) (@lem216348 c d h1)). Qed.
Lemma lem216353 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term38 a b c d) = (term41 a b c).
Proof. exact (MK_COMB (@lem216342 a c b d h1) (@lem216350 a b c d h1)). Qed.
Lemma lem216355 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem216356 (a : nat) (b : nat) (c : nat) : (term41 a b c) = True.
Proof. exact (@lem216355 ((Nat.div a b) = (term35 c))). Qed.
Lemma lem216357 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : (term38 a b c d) = True.
Proof. exact (TRANS (@lem216353 a b c d h1) (@lem216356 a b c)). Qed.
Lemma lem216358 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : True = (term38 a b c d).
Proof. exact (SYM (@lem216357 a b c d h1)). Qed.
Lemma lem216359 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : d = (NUMERAL 0)) : term38 a b c d.
Proof. exact (EQ_MP (@lem216358 a b c d h1) (@lem0)). Qed.
Lemma lem216440 (p : Prop) : p = (term42 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem216441 (a : nat) (b : nat) (c : nat) (d : nat) : (term38 a b c d) = (term43 a b c d).
Proof. exact (@lem216440 (term38 a b c d)). Qed.
Lemma lem216442 (a : nat) (b : nat) (c : nat) (d : nat) : (term43 a b c d) = (term38 a b c d).
Proof. exact (SYM (@lem216441 a b c d)). Qed.
Lemma lem216443 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term44 a b c d.
Proof. exact (h1). Qed.
Lemma lem216446 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term45 a b c d) : term45 a b c d.
Proof. exact (h1). Qed.
Lemma lem216447 (a : nat) (b : nat) (c : nat) (d : nat) : term46 a b c d.
Proof. exact (fun h0 : term45 a b c d => @lem216446 a b c d h0). Qed.
Lemma lem216448 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term46 a b c d) : term46 a b c d.
Proof. exact (h1). Qed.
Lemma lem216449 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term45 a b c d) : term45 a b c d.
Proof. exact (h1). Qed.
Lemma lem216450 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term45 a b c d) (h2 : term46 a b c d) : term45 a b c d.
Proof. exact (@lem216448 a b c d h2 (@lem216449 a b c d h1)). Qed.
Lemma lem216451 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term45 a b c d) : term47 a b c d.
Proof. exact (fun h0 : term46 a b c d => @lem216450 a b c d h1 h0). Qed.
Lemma lem216452 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term46 a b c d) : term46 a b c d.
Proof. exact (h1). Qed.
Lemma lem216453 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term45 a b c d) (h2 : term46 a b c d) : term45 a b c d.
Proof. exact (@lem216451 a b c d h1 (@lem216452 a b c d h2)). Qed.
Lemma lem216454 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term46 a b c d) : term46 a b c d.
Proof. exact (fun h0 : term45 a b c d => @lem216453 a b c d h0 h1). Qed.
Lemma lem216455 (a : nat) (b : nat) (c : nat) (d : nat) : term48 a b c d.
Proof. exact (fun h0 : term46 a b c d => @lem216454 a b c d h0). Qed.
Lemma lem216458 (a : nat) (b : nat) (c : nat) (d : nat) : term46 a b c d.
Proof. exact (@lem216455 a b c d (@lem216447 a b c d)). Qed.
Lemma lem216520 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem216521 : term49 = term50.
Proof. exact (@lem216520 term51). Qed.
Lemma lem216530 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem216531 : term53 = term54.
Proof. exact (MK_COMB (@lem216530) (@lem216521)). Qed.
Lemma lem216534 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem216535 : term56 = term57.
Proof. exact (MK_COMB (@lem216534) (@lem216531)). Qed.
Lemma lem216538 (a : nat) (b : nat) (c : nat) (d : nat) : (term58 a b c d) = (term58 a b c d).
Proof. exact (eq_refl (term58 a b c d)). Qed.
Lemma lem216539 (a : nat) (b : nat) (c : nat) (d : nat) : (term59 a b c d) = (term60 a b c d).
Proof. exact (MK_COMB (@lem216538 a b c d) (@lem216535)). Qed.
Lemma lem216542 (d : nat) : (term61 d) = (term61 d).
Proof. exact (eq_refl (term61 d)). Qed.
Lemma lem216543 (a : nat) (b : nat) (c : nat) (d : nat) : (term62 a b c d) = (term63 a b c d).
Proof. exact (MK_COMB (@lem216542 d) (@lem216539 a b c d)). Qed.
Lemma lem216546 (b : nat) : (term61 b) = (term61 b).
Proof. exact (eq_refl (term61 b)). Qed.
Lemma lem216547 (a : nat) (b : nat) (c : nat) (d : nat) : (term45 a b c d) = (term64 a b c d).
Proof. exact (MK_COMB (@lem216546 b) (@lem216543 a b c d)). Qed.
Lemma lem216550 (b : nat) (c : nat) (d : nat) : (term65 b c d) = (term66 b c d).
Proof. exact (fun_ext (fun a : nat => @lem216547 a b c d)). Qed.
Lemma lem216551 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216552 (b : nat) (c : nat) (d : nat) : (term67 b c d) = (term68 b c d).
Proof. exact (MK_COMB (@lem216551) (@lem216550 b c d)). Qed.
Lemma lem216557 (c : nat) (d : nat) : (term69 c d) = (term70 c d).
Proof. exact (fun_ext (fun b : nat => @lem216552 b c d)). Qed.
Lemma lem216558 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216559 (c : nat) (d : nat) : (term71 c d) = (term72 c d).
Proof. exact (MK_COMB (@lem216558) (@lem216557 c d)). Qed.
Lemma lem216564 (d : nat) : (term73 d) = (term74 d).
Proof. exact (fun_ext (fun c : nat => @lem216559 c d)). Qed.
Lemma lem216565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216566 (d : nat) : (term75 d) = (term76 d).
Proof. exact (MK_COMB (@lem216565) (@lem216564 d)). Qed.
Lemma lem216571 : term77 = term78.
Proof. exact (fun_ext (fun d : nat => @lem216566 d)). Qed.
Lemma lem216572 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216581 : term79 = term80.
Proof. exact (MK_COMB (@lem216572) (@lem216571)). Qed.
Lemma lem216582 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem216583 (m : nat) : (term81 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem216582 n m)). Qed.
Lemma lem216584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216585 (m : nat) : (term82 m) = (term82 m).
Proof. exact (MK_COMB (@lem216584) (@lem216583 m)). Qed.
Lemma lem216586 : term83 = term83.
Proof. exact (fun_ext (fun m : nat => @lem216585 m)). Qed.
Lemma lem216587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216588 : term51 = term51.
Proof. exact (MK_COMB (@lem216587) (@lem216586)). Qed.
Lemma lem216589 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem216590 : term50 = term50.
Proof. exact (MK_COMB (@lem216589) (@lem216588)). Qed.
Lemma lem216599 (m : nat) (n : nat) : ((term84 n m) = (m = n)) = ((term84 n m) = (m = n)).
Proof. exact (eq_refl ((term84 n m) = (m = n))). Qed.
Lemma lem216600 (m : nat) : (term85 m) = (term85 m).
Proof. exact (fun_ext (fun n : nat => @lem216599 m n)). Qed.
Lemma lem216601 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216602 (m : nat) : (term86 m) = (term86 m).
Proof. exact (MK_COMB (@lem216601) (@lem216600 m)). Qed.
Lemma lem216603 : term87 = term87.
Proof. exact (fun_ext (fun m : nat => @lem216602 m)). Qed.
Lemma lem216604 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216605 : term88 = term88.
Proof. exact (MK_COMB (@lem216604) (@lem216603)). Qed.
Lemma lem216606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem216607 : term52 = term52.
Proof. exact (MK_COMB (@lem216606) (@lem216605)). Qed.
Lemma lem216608 : term54 = term54.
Proof. exact (MK_COMB (@lem216607) (@lem216590)). Qed.
Lemma lem216619 (c : nat) (d : nat) (a : nat) (b : nat) : (term89 c d a b) = (term89 c d a b).
Proof. exact (eq_refl (term89 c d a b)). Qed.
Lemma lem216620 (c : nat) (a : nat) (b : nat) : (term90 c a b) = (term90 c a b).
Proof. exact (fun_ext (fun d : nat => @lem216619 c d a b)). Qed.
Lemma lem216621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216622 (c : nat) (a : nat) (b : nat) : (term91 c a b) = (term91 c a b).
Proof. exact (MK_COMB (@lem216621) (@lem216620 c a b)). Qed.
Lemma lem216623 (a : nat) (b : nat) : (term92 a b) = (term92 a b).
Proof. exact (fun_ext (fun c : nat => @lem216622 c a b)). Qed.
Lemma lem216624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216625 (a : nat) (b : nat) : (term93 a b) = (term93 a b).
Proof. exact (MK_COMB (@lem216624) (@lem216623 a b)). Qed.
Lemma lem216626 (a : nat) : (term94 a) = (term94 a).
Proof. exact (fun_ext (fun b : nat => @lem216625 a b)). Qed.
Lemma lem216627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216628 (a : nat) : (term95 a) = (term95 a).
Proof. exact (MK_COMB (@lem216627) (@lem216626 a)). Qed.
Lemma lem216629 : term96 = term96.
Proof. exact (fun_ext (fun a : nat => @lem216628 a)). Qed.
Lemma lem216630 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216631 : term97 = term97.
Proof. exact (MK_COMB (@lem216630) (@lem216629)). Qed.
Lemma lem216632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem216633 : term55 = term55.
Proof. exact (MK_COMB (@lem216632) (@lem216631)). Qed.
Lemma lem216634 : term57 = term57.
Proof. exact (MK_COMB (@lem216633) (@lem216608)). Qed.
Lemma lem216647 (a : nat) (b : nat) (c : nat) (d : nat) : (term58 a b c d) = (term58 a b c d).
Proof. exact (eq_refl (term58 a b c d)). Qed.
Lemma lem216648 (a : nat) (b : nat) (c : nat) (d : nat) : (term60 a b c d) = (term60 a b c d).
Proof. exact (MK_COMB (@lem216647 a b c d) (@lem216634)). Qed.
Lemma lem216653 (d : nat) : (term61 d) = (term61 d).
Proof. exact (eq_refl (term61 d)). Qed.
Lemma lem216654 (a : nat) (b : nat) (c : nat) (d : nat) : (term63 a b c d) = (term63 a b c d).
Proof. exact (MK_COMB (@lem216653 d) (@lem216648 a b c d)). Qed.
Lemma lem216659 (b : nat) : (term61 b) = (term61 b).
Proof. exact (eq_refl (term61 b)). Qed.
Lemma lem216660 (a : nat) (b : nat) (c : nat) (d : nat) : (term64 a b c d) = (term64 a b c d).
Proof. exact (MK_COMB (@lem216659 b) (@lem216654 a b c d)). Qed.
Lemma lem216661 (b : nat) (c : nat) (d : nat) : (term66 b c d) = (term66 b c d).
Proof. exact (fun_ext (fun a : nat => @lem216660 a b c d)). Qed.
Lemma lem216662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216663 (b : nat) (c : nat) (d : nat) : (term68 b c d) = (term68 b c d).
Proof. exact (MK_COMB (@lem216662) (@lem216661 b c d)). Qed.
Lemma lem216664 (c : nat) (d : nat) : (term70 c d) = (term70 c d).
Proof. exact (fun_ext (fun b : nat => @lem216663 b c d)). Qed.
Lemma lem216665 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216666 (c : nat) (d : nat) : (term72 c d) = (term72 c d).
Proof. exact (MK_COMB (@lem216665) (@lem216664 c d)). Qed.
Lemma lem216667 (d : nat) : (term74 d) = (term74 d).
Proof. exact (fun_ext (fun c : nat => @lem216666 c d)). Qed.
Lemma lem216668 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216669 (d : nat) : (term76 d) = (term76 d).
Proof. exact (MK_COMB (@lem216668) (@lem216667 d)). Qed.
Lemma lem216670 : term78 = term78.
Proof. exact (fun_ext (fun d : nat => @lem216669 d)). Qed.
Lemma lem216671 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216672 : term80 = term80.
Proof. exact (MK_COMB (@lem216671) (@lem216670)). Qed.
Lemma lem216767 : term79 = term80.
Proof. exact (TRANS (@lem216581) (@lem216672)). Qed.
Lemma lem216768 : term80 = term79.
Proof. exact (SYM (@lem216767)). Qed.
Lemma lem216771 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term44 a b c d.
Proof. exact (h1). Qed.
Lemma lem216772 (h1 : term97) : term97.
Proof. exact (h1). Qed.
Lemma lem216773 (h1 : term88) : term88.
Proof. exact (h1). Qed.
Lemma lem216774 (h1 : term51) : term51.
Proof. exact (h1). Qed.
Lemma lem216780 (b : nat) (h1 : term9 b) : term9 b.
Proof. exact (h1). Qed.
Lemma lem216786 (d : nat) (h1 : term9 d) : term9 d.
Proof. exact (h1). Qed.
Lemma lem216801 (a : nat) (b : nat) (c : nat) (d : nat) : (term44 a b c d) = (term98 a b c d).
Proof. exact (@lem17362 (term32 a d c b) ((Nat.div a b) = (Nat.div c d))). Qed.
Lemma lem216805 (b : nat) : (term99 b) = (b = (NUMERAL 0)).
Proof. exact (@lem16933 (b = (NUMERAL 0))). Qed.
Lemma lem216806 (b : nat) (c : nat) (a : nat) (d : nat) : (term100 b c a d) = (term100 b c a d).
Proof. exact (eq_refl (term100 b c a d)). Qed.
Lemma lem216807 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem216808 (b : nat) : (term101 b) = (term102 b).
Proof. exact (MK_COMB (@lem216807) (@lem216805 b)). Qed.
Lemma lem216809 (b : nat) (c : nat) (a : nat) (d : nat) : (term103 b c a d) = (term104 b c a d).
Proof. exact (MK_COMB (@lem216808 b) (@lem216806 b c a d)). Qed.
Lemma lem216810 (b : nat) (c : nat) (a : nat) (d : nat) : (term105 b c a d) = (term103 b c a d).
Proof. exact (@lem17045 (term9 b) (term24 b c a d)). Qed.
Lemma lem216811 (b : nat) (c : nat) (a : nat) (d : nat) : (term105 b c a d) = (term104 b c a d).
Proof. exact (TRANS (@lem216810 b c a d) (@lem216809 b c a d)). Qed.
Lemma lem216812 (c : nat) (d : nat) (a : nat) (b : nat) : (term106 c d a b) = (term106 c d a b).
Proof. exact (eq_refl (term106 c d a b)). Qed.
Lemma lem216813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem216814 (b : nat) (c : nat) (a : nat) (d : nat) : (term107 b c a d) = (term108 b c a d).
Proof. exact (MK_COMB (@lem216813) (@lem216811 b c a d)). Qed.
Lemma lem216815 (c : nat) (d : nat) (a : nat) (b : nat) : (term109 c d a b) = (term110 c d a b).
Proof. exact (MK_COMB (@lem216814 b c a d) (@lem216812 c d a b)). Qed.
Lemma lem216816 (c : nat) (d : nat) (a : nat) (b : nat) : (term89 c d a b) = (term109 c d a b).
Proof. exact (@lem17265 (term111 b c a d) (term106 c d a b)). Qed.
Lemma lem216817 (c : nat) (d : nat) (a : nat) (b : nat) : (term89 c d a b) = (term110 c d a b).
Proof. exact (TRANS (@lem216816 c d a b) (@lem216815 c d a b)). Qed.
Lemma lem216818 (c : nat) (a : nat) (b : nat) : (term90 c a b) = (term112 c a b).
Proof. exact (fun_ext (fun d : nat => @lem216817 c d a b)). Qed.
Lemma lem216819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216820 (c : nat) (a : nat) (b : nat) : (term91 c a b) = (term113 c a b).
Proof. exact (MK_COMB (@lem216819) (@lem216818 c a b)). Qed.
Lemma lem216821 (a : nat) (b : nat) : (term92 a b) = (term114 a b).
Proof. exact (fun_ext (fun c : nat => @lem216820 c a b)). Qed.
Lemma lem216822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216823 (a : nat) (b : nat) : (term93 a b) = (term115 a b).
Proof. exact (MK_COMB (@lem216822) (@lem216821 a b)). Qed.
Lemma lem216824 (a : nat) : (term94 a) = (term116 a).
Proof. exact (fun_ext (fun b : nat => @lem216823 a b)). Qed.
Lemma lem216825 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216826 (a : nat) : (term95 a) = (term117 a).
Proof. exact (MK_COMB (@lem216825) (@lem216824 a)). Qed.
Lemma lem216827 : term96 = term118.
Proof. exact (fun_ext (fun a : nat => @lem216826 a)). Qed.
Lemma lem216828 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216893 : term97 = term119.
Proof. exact (MK_COMB (@lem216828) (@lem216827)). Qed.
Lemma lem216894 (h1 : term97) : term119.
Proof. exact (EQ_MP (@lem216893) (@lem216772 h1)). Qed.
Lemma lem216903 (n : nat) (m : nat) : (term120 n m) = (term121 n m).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n m)). Qed.
Lemma lem216908 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem216909 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem216910 (n : nat) (m : nat) : (term122 n m) = (term123 n m).
Proof. exact (MK_COMB (@lem216909) (@lem216903 n m)). Qed.
Lemma lem216911 (m : nat) (n : nat) : (term124 m n) = (term125 m n).
Proof. exact (MK_COMB (@lem216910 n m) (@lem216908 m n)). Qed.
Lemma lem216916 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem216917 (m : nat) (n : nat) : (term127 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem216916 m n) (@lem216911 m n)). Qed.
Lemma lem216918 (m : nat) (n : nat) : ((term84 n m) = (m = n)) = (term127 m n).
Proof. exact (@lem17784 (term84 n m) (m = n)). Qed.
Lemma lem216919 (m : nat) (n : nat) : ((term84 n m) = (m = n)) = (term128 m n).
Proof. exact (TRANS (@lem216918 m n) (@lem216917 m n)). Qed.
Lemma lem216920 (m : nat) : (term85 m) = (term129 m).
Proof. exact (fun_ext (fun n : nat => @lem216919 m n)). Qed.
Lemma lem216921 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216922 (m : nat) : (term86 m) = (term130 m).
Proof. exact (MK_COMB (@lem216921) (@lem216920 m)). Qed.
Lemma lem216923 : term87 = term131.
Proof. exact (fun_ext (fun m : nat => @lem216922 m)). Qed.
Lemma lem216924 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216925 : term88 = term132.
Proof. exact (MK_COMB (@lem216924) (@lem216923)). Qed.
Lemma lem216931 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem216932 (P : nat -> Prop) (Q : nat -> Prop) : (term135 P Q) = (term136 P Q).
Proof. exact (@lem216931 nat P Q). Qed.
Lemma lem216933 (m : nat) : (term137 m) = (term138 m).
Proof. exact (@lem216932 (term139 m) (term140 m)). Qed.
Lemma lem216934 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (eq_refl (term141 m n)). Qed.
Lemma lem216935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem216936 (m : nat) (n : nat) : (term143 m n) = (term126 m n).
Proof. exact (MK_COMB (@lem216935) (@lem216934 m n)). Qed.
Lemma lem216937 (m : nat) (n : nat) : (term144 m n) = (term125 m n).
Proof. exact (eq_refl (term144 m n)). Qed.
Lemma lem216938 (m : nat) (n : nat) : (term145 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem216936 m n) (@lem216937 m n)). Qed.
Lemma lem216939 (m : nat) : (term146 m) = (term129 m).
Proof. exact (fun_ext (fun n : nat => @lem216938 m n)). Qed.
Lemma lem216940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216941 (m : nat) : (term137 m) = (term130 m).
Proof. exact (MK_COMB (@lem216940) (@lem216939 m)). Qed.
Lemma lem216942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem216943 (m : nat) : (term147 m) = (term148 m).
Proof. exact (MK_COMB (@lem216942) (@lem216941 m)). Qed.
Lemma lem216944 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (eq_refl (term141 m n)). Qed.
Lemma lem216945 (m : nat) : (term149 m) = (term139 m).
Proof. exact (fun_ext (fun n : nat => @lem216944 m n)). Qed.
Lemma lem216946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216947 (m : nat) : (term150 m) = (term151 m).
Proof. exact (MK_COMB (@lem216946) (@lem216945 m)). Qed.
Lemma lem216948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem216949 (m : nat) : (term152 m) = (term153 m).
Proof. exact (MK_COMB (@lem216948) (@lem216947 m)). Qed.
Lemma lem216950 (m : nat) (n : nat) : (term144 m n) = (term125 m n).
Proof. exact (eq_refl (term144 m n)). Qed.
Lemma lem216951 (m : nat) : (term154 m) = (term140 m).
Proof. exact (fun_ext (fun n : nat => @lem216950 m n)). Qed.
Lemma lem216952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem216953 (m : nat) : (term155 m) = (term156 m).
Proof. exact (MK_COMB (@lem216952) (@lem216951 m)). Qed.
Lemma lem216954 (m : nat) : (term138 m) = (term157 m).
Proof. exact (MK_COMB (@lem216949 m) (@lem216953 m)). Qed.
Lemma lem216955 (m : nat) : ((term137 m) = (term138 m)) = ((term130 m) = (term157 m)).
Proof. exact (MK_COMB (@lem216943 m) (@lem216954 m)). Qed.
Lemma lem216956 (m : nat) : (term130 m) = (term157 m).
Proof. exact (EQ_MP (@lem216955 m) (@lem216933 m)). Qed.
Lemma lem217053 : term131 = term158.
Proof. exact (fun_ext (fun m : nat => @lem216956 m)). Qed.
Lemma lem217054 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217055 : term132 = term159.
Proof. exact (MK_COMB (@lem217054) (@lem217053)). Qed.
Lemma lem217057 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = (term134 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem217058 (P : nat -> Prop) (Q : nat -> Prop) : (term135 P Q) = (term136 P Q).
Proof. exact (@lem217057 nat P Q). Qed.
Lemma lem217059 : term160 = term161.
Proof. exact (@lem217058 term162 term163). Qed.
Lemma lem217060 (m : nat) : (term164 m) = (term151 m).
Proof. exact (eq_refl (term164 m)). Qed.
Lemma lem217061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem217062 (m : nat) : (term165 m) = (term153 m).
Proof. exact (MK_COMB (@lem217061) (@lem217060 m)). Qed.
Lemma lem217063 (m : nat) : (term166 m) = (term156 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem217064 (m : nat) : (term167 m) = (term157 m).
Proof. exact (MK_COMB (@lem217062 m) (@lem217063 m)). Qed.
Lemma lem217065 : term168 = term158.
Proof. exact (fun_ext (fun m : nat => @lem217064 m)). Qed.
Lemma lem217066 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217067 : term160 = term159.
Proof. exact (MK_COMB (@lem217066) (@lem217065)). Qed.
Lemma lem217068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem217069 : term169 = term170.
Proof. exact (MK_COMB (@lem217068) (@lem217067)). Qed.
Lemma lem217070 (m : nat) : (term164 m) = (term151 m).
Proof. exact (eq_refl (term164 m)). Qed.
Lemma lem217071 : term171 = term162.
Proof. exact (fun_ext (fun m : nat => @lem217070 m)). Qed.
Lemma lem217072 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217073 : term172 = term173.
Proof. exact (MK_COMB (@lem217072) (@lem217071)). Qed.
Lemma lem217074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem217075 : term174 = term175.
Proof. exact (MK_COMB (@lem217074) (@lem217073)). Qed.
Lemma lem217076 (m : nat) : (term166 m) = (term156 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem217077 : term176 = term163.
Proof. exact (fun_ext (fun m : nat => @lem217076 m)). Qed.
Lemma lem217078 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217079 : term177 = term178.
Proof. exact (MK_COMB (@lem217078) (@lem217077)). Qed.
Lemma lem217080 : term161 = term179.
Proof. exact (MK_COMB (@lem217075) (@lem217079)). Qed.
Lemma lem217081 : (term160 = term161) = (term159 = term179).
Proof. exact (MK_COMB (@lem217069) (@lem217080)). Qed.
Lemma lem217082 : term159 = term179.
Proof. exact (EQ_MP (@lem217081) (@lem217059)). Qed.
Lemma lem217189 : term132 = term179.
Proof. exact (TRANS (@lem217055) (@lem217082)). Qed.
Lemma lem217190 : term88 = term179.
Proof. exact (TRANS (@lem216925) (@lem217189)). Qed.
Lemma lem217191 (h1 : term88) : term179.
Proof. exact (EQ_MP (@lem217190) (@lem216773 h1)). Qed.
Lemma lem217192 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem217193 (m : nat) : (term81 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem217192 n m)). Qed.
Lemma lem217194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217195 (m : nat) : (term82 m) = (term82 m).
Proof. exact (MK_COMB (@lem217194) (@lem217193 m)). Qed.
Lemma lem217196 : term83 = term83.
Proof. exact (fun_ext (fun m : nat => @lem217195 m)). Qed.
Lemma lem217197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217210 : term51 = term51.
Proof. exact (MK_COMB (@lem217197) (@lem217196)). Qed.
Lemma lem217211 (h1 : term51) : term51.
Proof. exact (EQ_MP (@lem217210) (@lem216774 h1)). Qed.
Lemma lem217221 (b : nat) (h1 : term9 b) : term9 b.
Proof. exact (h1). Qed.
Lemma lem217231 (d : nat) (h1 : term9 d) : term9 d.
Proof. exact (h1). Qed.
Lemma lem217295 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term98 a b c d.
Proof. exact (EQ_MP (@lem216801 a b c d) (@lem216771 a b c d h1)). Qed.
Lemma lem217344 (c : nat) (d : nat) (a : nat) (b : nat) : (term110 c d a b) = (term110 c d a b).
Proof. exact (eq_refl (term110 c d a b)). Qed.
Lemma lem217345 (c : nat) (a : nat) (b : nat) : (term112 c a b) = (term112 c a b).
Proof. exact (fun_ext (fun d : nat => @lem217344 c d a b)). Qed.
Lemma lem217346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217347 (c : nat) (a : nat) (b : nat) : (term113 c a b) = (term113 c a b).
Proof. exact (MK_COMB (@lem217346) (@lem217345 c a b)). Qed.
Lemma lem217348 (a : nat) (b : nat) : (term114 a b) = (term114 a b).
Proof. exact (fun_ext (fun c : nat => @lem217347 c a b)). Qed.
Lemma lem217349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217350 (a : nat) (b : nat) : (term115 a b) = (term115 a b).
Proof. exact (MK_COMB (@lem217349) (@lem217348 a b)). Qed.
Lemma lem217351 (a : nat) : (term116 a) = (term116 a).
Proof. exact (fun_ext (fun b : nat => @lem217350 a b)). Qed.
Lemma lem217352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217353 (a : nat) : (term117 a) = (term117 a).
Proof. exact (MK_COMB (@lem217352) (@lem217351 a)). Qed.
Lemma lem217354 : term118 = term118.
Proof. exact (fun_ext (fun a : nat => @lem217353 a)). Qed.
Lemma lem217355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217356 : term119 = term119.
Proof. exact (MK_COMB (@lem217355) (@lem217354)). Qed.
Lemma lem217357 (h1 : term97) : term119.
Proof. exact (EQ_MP (@lem217356) (@lem216894 h1)). Qed.
Lemma lem217382 (m : nat) (n : nat) : (term125 m n) = (term125 m n).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem217383 (m : nat) : (term140 m) = (term140 m).
Proof. exact (fun_ext (fun n : nat => @lem217382 m n)). Qed.
Lemma lem217384 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217385 (m : nat) : (term156 m) = (term156 m).
Proof. exact (MK_COMB (@lem217384) (@lem217383 m)). Qed.
Lemma lem217386 : term163 = term163.
Proof. exact (fun_ext (fun m : nat => @lem217385 m)). Qed.
Lemma lem217387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217388 : term178 = term178.
Proof. exact (MK_COMB (@lem217387) (@lem217386)). Qed.
Lemma lem217411 (m : nat) (n : nat) : (term142 m n) = (term142 m n).
Proof. exact (eq_refl (term142 m n)). Qed.
Lemma lem217412 (m : nat) : (term139 m) = (term139 m).
Proof. exact (fun_ext (fun n : nat => @lem217411 m n)). Qed.
Lemma lem217413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217414 (m : nat) : (term151 m) = (term151 m).
Proof. exact (MK_COMB (@lem217413) (@lem217412 m)). Qed.
Lemma lem217415 : term162 = term162.
Proof. exact (fun_ext (fun m : nat => @lem217414 m)). Qed.
Lemma lem217416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217417 : term173 = term173.
Proof. exact (MK_COMB (@lem217416) (@lem217415)). Qed.
Lemma lem217418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem217419 : term175 = term175.
Proof. exact (MK_COMB (@lem217418) (@lem217417)). Qed.
Lemma lem217420 : term179 = term179.
Proof. exact (MK_COMB (@lem217419) (@lem217388)). Qed.
Lemma lem217421 (h1 : term88) : term179.
Proof. exact (EQ_MP (@lem217420) (@lem217191 h1)). Qed.
Lemma lem217434 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem217435 (m : nat) : (term81 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem217434 n m)). Qed.
Lemma lem217436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217437 (m : nat) : (term82 m) = (term82 m).
Proof. exact (MK_COMB (@lem217436) (@lem217435 m)). Qed.
Lemma lem217438 : term83 = term83.
Proof. exact (fun_ext (fun m : nat => @lem217437 m)). Qed.
Lemma lem217439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217440 : term51 = term51.
Proof. exact (MK_COMB (@lem217439) (@lem217438)). Qed.
Lemma lem217441 (h1 : term51) : term51.
Proof. exact (EQ_MP (@lem217440) (@lem217211 h1)). Qed.
Lemma lem217442 (h1 : term88) : term178.
Proof. exact (proj2 (@lem217421 h1)). Qed.
Lemma lem217445 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term32 a d c b.
Proof. exact (proj1 (@lem217295 a b c d h1)). Qed.
Lemma lem217451 (b : nat) (h1 : term9 b) : term9 b.
Proof. exact (h1). Qed.
Lemma lem217455 (d : nat) (h1 : term9 d) : term9 d.
Proof. exact (h1). Qed.
Lemma lem217469 (c : nat) (d : nat) (a : nat) (b : nat) : (term110 c d a b) = (term110 c d a b).
Proof. exact (eq_refl (term110 c d a b)). Qed.
Lemma lem217470 (c : nat) (a : nat) (b : nat) : (term112 c a b) = (term112 c a b).
Proof. exact (fun_ext (fun d : nat => @lem217469 c d a b)). Qed.
Lemma lem217471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217472 (c : nat) (a : nat) (b : nat) : (term113 c a b) = (term113 c a b).
Proof. exact (MK_COMB (@lem217471) (@lem217470 c a b)). Qed.
Lemma lem217473 (a : nat) (b : nat) : (term114 a b) = (term114 a b).
Proof. exact (fun_ext (fun c : nat => @lem217472 c a b)). Qed.
Lemma lem217474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217475 (a : nat) (b : nat) : (term115 a b) = (term115 a b).
Proof. exact (MK_COMB (@lem217474) (@lem217473 a b)). Qed.
Lemma lem217476 (a : nat) : (term116 a) = (term116 a).
Proof. exact (fun_ext (fun b : nat => @lem217475 a b)). Qed.
Lemma lem217477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217478 (a : nat) : (term117 a) = (term117 a).
Proof. exact (MK_COMB (@lem217477) (@lem217476 a)). Qed.
Lemma lem217479 : term118 = term118.
Proof. exact (fun_ext (fun a : nat => @lem217478 a)). Qed.
Lemma lem217480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217482 : term119 = term119.
Proof. exact (MK_COMB (@lem217480) (@lem217479)). Qed.
Lemma lem217483 (h1 : term97) : term119.
Proof. exact (EQ_MP (@lem217482) (@lem217357 h1)). Qed.
Lemma lem217485 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem217486 (m : nat) : (term81 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem217485 n m)). Qed.
Lemma lem217487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217488 (m : nat) : (term82 m) = (term82 m).
Proof. exact (MK_COMB (@lem217487) (@lem217486 m)). Qed.
Lemma lem217489 : term83 = term83.
Proof. exact (fun_ext (fun m : nat => @lem217488 m)). Qed.
Lemma lem217490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217492 : term51 = term51.
Proof. exact (MK_COMB (@lem217490) (@lem217489)). Qed.
Lemma lem217493 (h1 : term51) : term51.
Proof. exact (EQ_MP (@lem217492) (@lem217441 h1)). Qed.
Lemma lem217533 (m : nat) (n : nat) : (term125 m n) = (term125 m n).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem217534 (m : nat) : (term140 m) = (term140 m).
Proof. exact (fun_ext (fun n : nat => @lem217533 m n)). Qed.
Lemma lem217535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217536 (m : nat) : (term156 m) = (term156 m).
Proof. exact (MK_COMB (@lem217535) (@lem217534 m)). Qed.
Lemma lem217537 : term163 = term163.
Proof. exact (fun_ext (fun m : nat => @lem217536 m)). Qed.
Lemma lem217538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem217540 : term178 = term178.
Proof. exact (MK_COMB (@lem217538) (@lem217537)). Qed.
Lemma lem217541 (h1 : term88) : term178.
Proof. exact (EQ_MP (@lem217540) (@lem217442 h1)). Qed.
Lemma lem217554 (_4356 : nat) (h1 : term97) : term180 _4356.
Proof. exact (@lem217483 h1 _4356). Qed.
Lemma lem217555 (_4356 : nat) : (term180 _4356) = (term117 _4356).
Proof. exact (eq_refl (term180 _4356)). Qed.
Lemma lem217556 (_4356 : nat) (h1 : term97) : term117 _4356.
Proof. exact (EQ_MP (@lem217555 _4356) (@lem217554 _4356 h1)). Qed.
Lemma lem217557 (_4356 : nat) (_4357 : nat) (h1 : term97) : term181 _4356 _4357.
Proof. exact (@lem217556 _4356 h1 _4357). Qed.
Lemma lem217558 (_4356 : nat) (_4357 : nat) : (term181 _4356 _4357) = (term115 _4356 _4357).
Proof. exact (eq_refl (term181 _4356 _4357)). Qed.
Lemma lem217559 (_4356 : nat) (_4357 : nat) (h1 : term97) : term115 _4356 _4357.
Proof. exact (EQ_MP (@lem217558 _4356 _4357) (@lem217557 _4356 _4357 h1)). Qed.
Lemma lem217560 (_4356 : nat) (_4357 : nat) (_4358 : nat) (h1 : term97) : term182 _4356 _4357 _4358.
Proof. exact (@lem217559 _4356 _4357 h1 _4358). Qed.
Lemma lem217561 (_4358 : nat) (_4356 : nat) (_4357 : nat) : (term182 _4356 _4357 _4358) = (term113 _4358 _4356 _4357).
Proof. exact (eq_refl (term182 _4356 _4357 _4358)). Qed.
Lemma lem217562 (_4358 : nat) (_4356 : nat) (_4357 : nat) (h1 : term97) : term113 _4358 _4356 _4357.
Proof. exact (EQ_MP (@lem217561 _4358 _4356 _4357) (@lem217560 _4356 _4357 _4358 h1)). Qed.
Lemma lem217563 (_4358 : nat) (_4356 : nat) (_4357 : nat) (_4359 : nat) (h1 : term97) : term183 _4358 _4356 _4357 _4359.
Proof. exact (@lem217562 _4358 _4356 _4357 h1 _4359). Qed.
Lemma lem217564 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) : (term183 _4358 _4356 _4357 _4359) = (term110 _4358 _4359 _4356 _4357).
Proof. exact (eq_refl (term183 _4358 _4356 _4357 _4359)). Qed.
Lemma lem217565 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) (h1 : term97) : term110 _4358 _4359 _4356 _4357.
Proof. exact (EQ_MP (@lem217564 _4358 _4359 _4356 _4357) (@lem217563 _4358 _4356 _4357 _4359 h1)). Qed.
Lemma lem217566 (_4360 : nat) (h1 : term51) : term184 _4360.
Proof. exact (@lem217493 h1 _4360). Qed.
Lemma lem217567 (_4360 : nat) : (term184 _4360) = (term82 _4360).
Proof. exact (eq_refl (term184 _4360)). Qed.
Lemma lem217568 (_4360 : nat) (h1 : term51) : term82 _4360.
Proof. exact (EQ_MP (@lem217567 _4360) (@lem217566 _4360 h1)). Qed.
Lemma lem217569 (_4360 : nat) (_4361 : nat) (h1 : term51) : term185 _4360 _4361.
Proof. exact (@lem217568 _4360 h1 _4361). Qed.
Lemma lem217570 (_4361 : nat) (_4360 : nat) : (term185 _4360 _4361) = ((Nat.mul _4360 _4361) = (Nat.mul _4361 _4360)).
Proof. exact (eq_refl (term185 _4360 _4361)). Qed.
Lemma lem217578 (_4364 : nat) (h1 : term88) : term166 _4364.
Proof. exact (@lem217541 h1 _4364). Qed.
Lemma lem217579 (_4364 : nat) : (term166 _4364) = (term156 _4364).
Proof. exact (eq_refl (term166 _4364)). Qed.
Lemma lem217580 (_4364 : nat) (h1 : term88) : term156 _4364.
Proof. exact (EQ_MP (@lem217579 _4364) (@lem217578 _4364 h1)). Qed.
Lemma lem217581 (_4364 : nat) (_4365 : nat) (h1 : term88) : term144 _4364 _4365.
Proof. exact (@lem217580 _4364 h1 _4365). Qed.
Lemma lem217582 (_4364 : nat) (_4365 : nat) : (term144 _4364 _4365) = (term125 _4364 _4365).
Proof. exact (eq_refl (term144 _4364 _4365)). Qed.
Lemma lem217583 (_4364 : nat) (_4365 : nat) (h1 : term88) : term125 _4364 _4365.
Proof. exact (EQ_MP (@lem217582 _4364 _4365) (@lem217581 _4364 _4365 h1)). Qed.
Lemma lem217587 (b : nat) (h1 : term9 b) : term9 b.
Proof. exact (h1). Qed.
Lemma lem217589 (d : nat) (h1 : term9 d) : term9 d.
Proof. exact (h1). Qed.
Lemma lem217600 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) : (term110 _4358 _4359 _4356 _4357) = (term186 _4358 _4359 _4356 _4357).
Proof. exact (@lem216064 (_4357 = (NUMERAL 0)) (term100 _4357 _4358 _4356 _4359) (term106 _4358 _4359 _4356 _4357)). Qed.
Lemma lem217601 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) (h1 : term97) : term186 _4358 _4359 _4356 _4357.
Proof. exact (EQ_MP (@lem217600 _4358 _4359 _4356 _4357) (@lem217565 _4358 _4359 _4356 _4357 h1)). Qed.
Lemma lem217614 (_4364 : nat) (_4365 : nat) : (term125 _4364 _4365) = (term187 _4364 _4365).
Proof. exact (@lem216064 (term188 _4364 _4365) (term188 _4365 _4364) (_4364 = _4365)). Qed.
Lemma lem217615 (_4364 : nat) (_4365 : nat) (h1 : term88) : term187 _4364 _4365.
Proof. exact (EQ_MP (@lem217614 _4364 _4365) (@lem217583 _4364 _4365 h1)). Qed.
Lemma lem217617 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term189 a b c d.
Proof. exact (proj2 (@lem217295 a b c d h1)). Qed.
Lemma lem217634 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem217635 (_4366 : nat) (_4368 : nat) (h1 : _4366 = _4368) : _4366 = _4368.
Proof. exact (h1). Qed.
Lemma lem217636 (_4367 : nat) (_4369 : nat) (h1 : _4367 = _4369) : _4367 = _4369.
Proof. exact (h1). Qed.
Lemma lem217637 (_4366 : nat) (_4368 : nat) (h1 : _4366 = _4368) : (Peano.lt _4366) = (Peano.lt _4368).
Proof. exact (MK_COMB (@lem217634) (@lem217635 _4366 _4368 h1)). Qed.
Lemma lem217638 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) (h1 : _4366 = _4368) (h2 : _4367 = _4369) : (Peano.lt _4366 _4367) = (Peano.lt _4368 _4369).
Proof. exact (MK_COMB (@lem217637 _4366 _4368 h1) (@lem217636 _4367 _4369 h2)). Qed.
Lemma lem217640 (b : Prop) (a : Prop) : term190 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem217641 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : term191 _4368 _4369 _4366 _4367.
Proof. exact (@lem217640 (Peano.lt _4368 _4369) (Peano.lt _4366 _4367)). Qed.
Lemma lem217642 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) (h1 : _4366 = _4368) (h2 : _4367 = _4369) : term192 _4368 _4369 _4366 _4367.
Proof. exact (@lem217641 _4368 _4369 _4366 _4367 (@lem217638 _4366 _4368 _4367 _4369 h1 h2)). Qed.
Lemma lem217643 (_4369 : nat) (_4367 : nat) (_4366 : nat) (_4368 : nat) (h1 : _4366 = _4368) : term193 _4368 _4369 _4366 _4367.
Proof. exact (fun h0 : _4367 = _4369 => @lem217642 _4366 _4368 _4367 _4369 h1 h0). Qed.
Lemma lem217645 (a : Prop) (b : Prop) : (a -> b) = (term194 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem217646 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term193 _4368 _4369 _4366 _4367) = (term195 _4368 _4369 _4366 _4367).
Proof. exact (@lem217645 (_4367 = _4369) (term192 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217647 (_4369 : nat) (_4367 : nat) (_4366 : nat) (_4368 : nat) (h1 : _4366 = _4368) : term195 _4368 _4369 _4366 _4367.
Proof. exact (EQ_MP (@lem217646 _4368 _4369 _4366 _4367) (@lem217643 _4369 _4367 _4366 _4368 h1)). Qed.
Lemma lem217648 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : term196 _4368 _4369 _4366 _4367.
Proof. exact (fun h0 : _4366 = _4368 => @lem217647 _4369 _4367 _4366 _4368 h0). Qed.
Lemma lem217650 (a : Prop) (b : Prop) : (a -> b) = (term194 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem217651 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term196 _4368 _4369 _4366 _4367) = (term197 _4368 _4369 _4366 _4367).
Proof. exact (@lem217650 (_4366 = _4368) (term195 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217652 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : term197 _4368 _4369 _4366 _4367.
Proof. exact (EQ_MP (@lem217651 _4368 _4369 _4366 _4367) (@lem217648 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217736 (d : nat) (h1 : term9 d) : term9 d.
Proof. exact (h1). Qed.
Lemma lem217737 (d : nat) (h1 : term9 d) : term198 d.
Proof. exact (fun h0 : d = (NUMERAL 0) => @lem217736 d h1). Qed.
Lemma lem217739 (p : Prop) : (term199 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem217740 (d : nat) : (term198 d) = (term9 d).
Proof. exact (@lem217739 (d = (NUMERAL 0))). Qed.
Lemma lem217741 (d : nat) (h1 : term9 d) : term9 d.
Proof. exact (EQ_MP (@lem217740 d) (@lem217737 d h1)). Qed.
Lemma lem217743 (_4361 : nat) (_4360 : nat) (h1 : term51) : (Nat.mul _4360 _4361) = (Nat.mul _4361 _4360).
Proof. exact (EQ_MP (@lem217570 _4361 _4360) (@lem217569 _4360 _4361 h1)). Qed.
Lemma lem217744 (d : nat) (a : nat) (h1 : term51) : (Nat.mul a d) = (Nat.mul d a).
Proof. exact (@lem217743 d a h1). Qed.
Lemma lem217745 (d : nat) (a : nat) (h1 : term51) : term200 d a.
Proof. exact (fun h0 : term201 d a => @lem217744 d a h1). Qed.
Lemma lem217747 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem217748 (d : nat) (a : nat) : (term200 d a) = ((Nat.mul a d) = (Nat.mul d a)).
Proof. exact (@lem217747 ((Nat.mul a d) = (Nat.mul d a))). Qed.
Lemma lem217749 (d : nat) (a : nat) (h1 : term51) : (Nat.mul a d) = (Nat.mul d a).
Proof. exact (EQ_MP (@lem217748 d a) (@lem217745 d a h1)). Qed.
Lemma lem217751 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem217752 (c : nat) (b : nat) : (term23 c b) = (term23 c b).
Proof. exact (@lem217751 (term23 c b)). Qed.
Lemma lem217753 (c : nat) (b : nat) : term203 c b.
Proof. exact (fun h0 : term204 c b => @lem217752 c b). Qed.
Lemma lem217755 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem217756 (c : nat) (b : nat) : (term203 c b) = ((term23 c b) = (term23 c b)).
Proof. exact (@lem217755 ((term23 c b) = (term23 c b))). Qed.
Lemma lem217757 (c : nat) (b : nat) : (term23 c b) = (term23 c b).
Proof. exact (EQ_MP (@lem217756 c b) (@lem217753 c b)). Qed.
Lemma lem217759 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term24 a d c b.
Proof. exact (proj2 (@lem217445 a b c d h1)). Qed.
Lemma lem217760 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term205 a d c b.
Proof. exact (fun h0 : term100 a d c b => @lem217759 a b c d h1). Qed.
Lemma lem217762 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem217763 (a : nat) (d : nat) (c : nat) (b : nat) : (term205 a d c b) = (term24 a d c b).
Proof. exact (@lem217762 (term24 a d c b)). Qed.
Lemma lem217764 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term24 a d c b.
Proof. exact (EQ_MP (@lem217763 a d c b) (@lem217760 a b c d h1)). Qed.
Lemma lem217782 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem217783 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term195 _4368 _4369 _4366 _4367) = (term206 _4368 _4369 _4366 _4367).
Proof. exact (@lem217782 (Peano.lt _4368 _4369) (term207 _4367 _4369) (term208 _4366 _4367)). Qed.
Lemma lem217797 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem217798 (_4366 : nat) (_4367 : nat) (_4369 : nat) : (term209 _4369 _4366 _4367) = (term210 _4366 _4367 _4369).
Proof. exact (@lem217797 (term208 _4366 _4367) (term207 _4367 _4369)). Qed.
Lemma lem217806 (_4368 : nat) (_4369 : nat) : (term211 _4368 _4369) = (term211 _4368 _4369).
Proof. exact (eq_refl (term211 _4368 _4369)). Qed.
Lemma lem217807 (_4368 : nat) (_4366 : nat) (_4367 : nat) (_4369 : nat) : (term206 _4368 _4369 _4366 _4367) = (term212 _4368 _4366 _4367 _4369).
Proof. exact (MK_COMB (@lem217806 _4368 _4369) (@lem217798 _4366 _4367 _4369)). Qed.
Lemma lem217818 (_4368 : nat) (_4366 : nat) (_4367 : nat) (_4369 : nat) : (term195 _4368 _4369 _4366 _4367) = (term212 _4368 _4366 _4367 _4369).
Proof. exact (TRANS (@lem217783 _4368 _4369 _4366 _4367) (@lem217807 _4368 _4366 _4367 _4369)). Qed.
Lemma lem217819 (_4366 : nat) (_4368 : nat) : (term213 _4366 _4368) = (term213 _4366 _4368).
Proof. exact (eq_refl (term213 _4366 _4368)). Qed.
Lemma lem217820 (_4368 : nat) (_4366 : nat) (_4367 : nat) (_4369 : nat) : (term197 _4368 _4369 _4366 _4367) = (term214 _4368 _4366 _4367 _4369).
Proof. exact (MK_COMB (@lem217819 _4366 _4368) (@lem217818 _4368 _4366 _4367 _4369)). Qed.
Lemma lem217824 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem217825 (_4368 : nat) (_4366 : nat) (_4367 : nat) (_4369 : nat) : (term214 _4368 _4366 _4367 _4369) = (term215 _4368 _4366 _4367 _4369).
Proof. exact (@lem217824 (Peano.lt _4368 _4369) (term207 _4366 _4368) (term210 _4366 _4367 _4369)). Qed.
Lemma lem217839 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem217840 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term216 _4368 _4366 _4367 _4369) = (term217 _4366 _4368 _4367 _4369).
Proof. exact (@lem217839 (term208 _4366 _4367) (term207 _4366 _4368) (term207 _4367 _4369)). Qed.
Lemma lem217860 (_4368 : nat) (_4369 : nat) : (term211 _4368 _4369) = (term211 _4368 _4369).
Proof. exact (eq_refl (term211 _4368 _4369)). Qed.
Lemma lem217861 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term215 _4368 _4366 _4367 _4369) = (term218 _4366 _4368 _4367 _4369).
Proof. exact (MK_COMB (@lem217860 _4368 _4369) (@lem217840 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217872 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term214 _4368 _4366 _4367 _4369) = (term218 _4366 _4368 _4367 _4369).
Proof. exact (TRANS (@lem217825 _4368 _4366 _4367 _4369) (@lem217861 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217873 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term197 _4368 _4369 _4366 _4367) = (term218 _4366 _4368 _4367 _4369).
Proof. exact (TRANS (@lem217820 _4368 _4366 _4367 _4369) (@lem217872 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem217875 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term219 _4368 _4369 _4366 _4367) = (term220 _4366 _4368 _4367 _4369).
Proof. exact (MK_COMB (@lem217874) (@lem217873 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217901 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem217902 (_4366 : nat) (_4367 : nat) (_4369 : nat) : (term209 _4369 _4366 _4367) = (term210 _4366 _4367 _4369).
Proof. exact (@lem217901 (term208 _4366 _4367) (term207 _4367 _4369)). Qed.
Lemma lem217910 (_4366 : nat) (_4368 : nat) : (term213 _4366 _4368) = (term213 _4366 _4368).
Proof. exact (eq_refl (term213 _4366 _4368)). Qed.
Lemma lem217911 (_4368 : nat) (_4366 : nat) (_4367 : nat) (_4369 : nat) : (term221 _4368 _4369 _4366 _4367) = (term216 _4368 _4366 _4367 _4369).
Proof. exact (MK_COMB (@lem217910 _4366 _4368) (@lem217902 _4366 _4367 _4369)). Qed.
Lemma lem217915 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem217916 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term216 _4368 _4366 _4367 _4369) = (term217 _4366 _4368 _4367 _4369).
Proof. exact (@lem217915 (term208 _4366 _4367) (term207 _4366 _4368) (term207 _4367 _4369)). Qed.
Lemma lem217936 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term221 _4368 _4369 _4366 _4367) = (term217 _4366 _4368 _4367 _4369).
Proof. exact (TRANS (@lem217911 _4368 _4366 _4367 _4369) (@lem217916 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217937 (_4368 : nat) (_4369 : nat) : (term211 _4368 _4369) = (term211 _4368 _4369).
Proof. exact (eq_refl (term211 _4368 _4369)). Qed.
Lemma lem217938 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : (term222 _4368 _4369 _4366 _4367) = (term218 _4366 _4368 _4367 _4369).
Proof. exact (MK_COMB (@lem217937 _4368 _4369) (@lem217936 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217949 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : ((term197 _4368 _4369 _4366 _4367) = (term222 _4368 _4369 _4366 _4367)) = ((term218 _4366 _4368 _4367 _4369) = (term218 _4366 _4368 _4367 _4369)).
Proof. exact (MK_COMB (@lem217875 _4366 _4368 _4367 _4369) (@lem217938 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217951 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem217952 (x : Prop) : (x = x) = True.
Proof. exact (@lem217951 Prop x). Qed.
Lemma lem217953 (_4366 : nat) (_4368 : nat) (_4367 : nat) (_4369 : nat) : ((term218 _4366 _4368 _4367 _4369) = (term218 _4366 _4368 _4367 _4369)) = True.
Proof. exact (@lem217952 (term218 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217954 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : ((term197 _4368 _4369 _4366 _4367) = (term222 _4368 _4369 _4366 _4367)) = True.
Proof. exact (TRANS (@lem217949 _4366 _4368 _4367 _4369) (@lem217953 _4366 _4368 _4367 _4369)). Qed.
Lemma lem217955 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : True = ((term197 _4368 _4369 _4366 _4367) = (term222 _4368 _4369 _4366 _4367)).
Proof. exact (SYM (@lem217954 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217956 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term197 _4368 _4369 _4366 _4367) = (term222 _4368 _4369 _4366 _4367).
Proof. exact (EQ_MP (@lem217955 _4368 _4369 _4366 _4367) (@lem0)). Qed.
Lemma lem217957 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : term222 _4368 _4369 _4366 _4367.
Proof. exact (EQ_MP (@lem217956 _4368 _4369 _4366 _4367) (@lem217652 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217959 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem217960 (_4366 : nat) (_4367 : nat) (_4368 : nat) (_4369 : nat) : (term222 _4368 _4369 _4366 _4367) = (term224 _4366 _4367 _4368 _4369).
Proof. exact (@lem217959 (term221 _4368 _4369 _4366 _4367) (Peano.lt _4368 _4369)). Qed.
Lemma lem217962 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem217963 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term227 _4368 _4369 _4366 _4367) = (term228 _4368 _4369 _4366 _4367).
Proof. exact (@lem217962 (term207 _4366 _4368) (term209 _4369 _4366 _4367)). Qed.
Lemma lem217965 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem217966 (_4366 : nat) (_4368 : nat) : (term230 _4366 _4368) = (_4366 = _4368).
Proof. exact (@lem217965 (_4366 = _4368)). Qed.
Lemma lem217967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem217968 (_4366 : nat) (_4368 : nat) : (term231 _4366 _4368) = (term232 _4366 _4368).
Proof. exact (MK_COMB (@lem217967) (@lem217966 _4366 _4368)). Qed.
Lemma lem217970 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem217971 (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term233 _4369 _4366 _4367) = (term234 _4369 _4366 _4367).
Proof. exact (@lem217970 (term207 _4367 _4369) (term208 _4366 _4367)). Qed.
Lemma lem217973 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem217974 (_4367 : nat) (_4369 : nat) : (term230 _4367 _4369) = (_4367 = _4369).
Proof. exact (@lem217973 (_4367 = _4369)). Qed.
Lemma lem217975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem217976 (_4367 : nat) (_4369 : nat) : (term231 _4367 _4369) = (term232 _4367 _4369).
Proof. exact (MK_COMB (@lem217975) (@lem217974 _4367 _4369)). Qed.
Lemma lem217978 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem217979 (_4366 : nat) (_4367 : nat) : (term235 _4366 _4367) = (Peano.lt _4366 _4367).
Proof. exact (@lem217978 (Peano.lt _4366 _4367)). Qed.
Lemma lem217980 (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term234 _4369 _4366 _4367) = (term236 _4369 _4366 _4367).
Proof. exact (MK_COMB (@lem217976 _4367 _4369) (@lem217979 _4366 _4367)). Qed.
Lemma lem217981 (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term233 _4369 _4366 _4367) = (term236 _4369 _4366 _4367).
Proof. exact (TRANS (@lem217971 _4369 _4366 _4367) (@lem217980 _4369 _4366 _4367)). Qed.
Lemma lem217982 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term228 _4368 _4369 _4366 _4367) = (term237 _4368 _4369 _4366 _4367).
Proof. exact (MK_COMB (@lem217968 _4366 _4368) (@lem217981 _4369 _4366 _4367)). Qed.
Lemma lem217983 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term227 _4368 _4369 _4366 _4367) = (term237 _4368 _4369 _4366 _4367).
Proof. exact (TRANS (@lem217963 _4368 _4369 _4366 _4367) (@lem217982 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem217985 (_4368 : nat) (_4369 : nat) (_4366 : nat) (_4367 : nat) : (term238 _4368 _4369 _4366 _4367) = (term239 _4368 _4369 _4366 _4367).
Proof. exact (MK_COMB (@lem217984) (@lem217983 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217986 (_4368 : nat) (_4369 : nat) : (Peano.lt _4368 _4369) = (Peano.lt _4368 _4369).
Proof. exact (eq_refl (Peano.lt _4368 _4369)). Qed.
Lemma lem217987 (_4366 : nat) (_4367 : nat) (_4368 : nat) (_4369 : nat) : (term224 _4366 _4367 _4368 _4369) = (term240 _4366 _4367 _4368 _4369).
Proof. exact (MK_COMB (@lem217985 _4368 _4369 _4366 _4367) (@lem217986 _4368 _4369)). Qed.
Lemma lem217988 (_4366 : nat) (_4367 : nat) (_4368 : nat) (_4369 : nat) : (term222 _4368 _4369 _4366 _4367) = (term240 _4366 _4367 _4368 _4369).
Proof. exact (TRANS (@lem217960 _4366 _4367 _4368 _4369) (@lem217987 _4366 _4367 _4368 _4369)). Qed.
Lemma lem217990 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term241 a d c b.
Proof. exact (conj (@lem217757 c b) (@lem217764 a b c d h1)). Qed.
Lemma lem217991 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term51) (h2 : term44 a b c d) : term242 a d c b.
Proof. exact (conj (@lem217749 d a h1) (@lem217990 a b c d h2)). Qed.
Lemma lem217993 (_4366 : nat) (_4367 : nat) (_4368 : nat) (_4369 : nat) : term240 _4366 _4367 _4368 _4369.
Proof. exact (EQ_MP (@lem217988 _4366 _4367 _4368 _4369) (@lem217957 _4368 _4369 _4366 _4367)). Qed.
Lemma lem217994 (d : nat) (a : nat) (c : nat) (b : nat) : term243 d a c b.
Proof. exact (@lem217993 (Nat.mul a d) (term23 c b) (Nat.mul d a) (term23 c b)). Qed.
Lemma lem217997 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term51) (h2 : term44 a b c d) : term24 d a c b.
Proof. exact (@lem217994 d a c b (@lem217991 a b c d h1 h2)). Qed.
Lemma lem217998 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term51) (h2 : term44 a b c d) : term205 d a c b.
Proof. exact (fun h0 : term100 d a c b => @lem217997 a b c d h1 h2). Qed.
Lemma lem218000 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem218001 (d : nat) (a : nat) (c : nat) (b : nat) : (term205 d a c b) = (term24 d a c b).
Proof. exact (@lem218000 (term24 d a c b)). Qed.
Lemma lem218002 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term51) (h2 : term44 a b c d) : term24 d a c b.
Proof. exact (EQ_MP (@lem218001 d a c b) (@lem217998 a b c d h1 h2)). Qed.
Lemma lem218020 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem218021 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term244 _4358 _4359 _4356 _4357) = (term245 _4357 _4358 _4356 _4359).
Proof. exact (@lem218020 (term106 _4358 _4359 _4356 _4357) (term100 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218027 (_4357 : nat) : (term102 _4357) = (term102 _4357).
Proof. exact (eq_refl (term102 _4357)). Qed.
Lemma lem218028 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term186 _4358 _4359 _4356 _4357) = (term246 _4357 _4358 _4356 _4359).
Proof. exact (MK_COMB (@lem218027 _4357) (@lem218021 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218032 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem218033 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term246 _4357 _4358 _4356 _4359) = (term247 _4357 _4358 _4356 _4359).
Proof. exact (@lem218032 (term106 _4358 _4359 _4356 _4357) (_4357 = (NUMERAL 0)) (term100 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218051 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term186 _4358 _4359 _4356 _4357) = (term247 _4357 _4358 _4356 _4359).
Proof. exact (TRANS (@lem218028 _4357 _4358 _4356 _4359) (@lem218033 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem218053 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term248 _4358 _4359 _4356 _4357) = (term249 _4357 _4358 _4356 _4359).
Proof. exact (MK_COMB (@lem218052) (@lem218051 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218071 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term247 _4357 _4358 _4356 _4359) = (term247 _4357 _4358 _4356 _4359).
Proof. exact (eq_refl (term247 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218072 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : ((term186 _4358 _4359 _4356 _4357) = (term247 _4357 _4358 _4356 _4359)) = ((term247 _4357 _4358 _4356 _4359) = (term247 _4357 _4358 _4356 _4359)).
Proof. exact (MK_COMB (@lem218053 _4357 _4358 _4356 _4359) (@lem218071 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem218075 (x : Prop) : (x = x) = True.
Proof. exact (@lem218074 Prop x). Qed.
Lemma lem218076 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : ((term247 _4357 _4358 _4356 _4359) = (term247 _4357 _4358 _4356 _4359)) = True.
Proof. exact (@lem218075 (term247 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218077 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : ((term186 _4358 _4359 _4356 _4357) = (term247 _4357 _4358 _4356 _4359)) = True.
Proof. exact (TRANS (@lem218072 _4357 _4358 _4356 _4359) (@lem218076 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218078 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : True = ((term186 _4358 _4359 _4356 _4357) = (term247 _4357 _4358 _4356 _4359)).
Proof. exact (SYM (@lem218077 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218079 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term186 _4358 _4359 _4356 _4357) = (term247 _4357 _4358 _4356 _4359).
Proof. exact (EQ_MP (@lem218078 _4357 _4358 _4356 _4359) (@lem0)). Qed.
Lemma lem218080 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) (h1 : term97) : term247 _4357 _4358 _4356 _4359.
Proof. exact (EQ_MP (@lem218079 _4357 _4358 _4356 _4359) (@lem217601 _4358 _4359 _4356 _4357 h1)). Qed.
Lemma lem218082 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem218083 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) : (term247 _4357 _4358 _4356 _4359) = (term250 _4358 _4359 _4356 _4357).
Proof. exact (@lem218082 (term104 _4357 _4358 _4356 _4359) (term106 _4358 _4359 _4356 _4357)). Qed.
Lemma lem218085 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem218086 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term251 _4357 _4358 _4356 _4359) = (term252 _4357 _4358 _4356 _4359).
Proof. exact (@lem218085 (_4357 = (NUMERAL 0)) (term100 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218088 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem218089 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term253 _4357 _4358 _4356 _4359) = (term24 _4357 _4358 _4356 _4359).
Proof. exact (@lem218088 (term24 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218090 (_4357 : nat) : (term254 _4357) = (term254 _4357).
Proof. exact (eq_refl (term254 _4357)). Qed.
Lemma lem218091 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term252 _4357 _4358 _4356 _4359) = (term111 _4357 _4358 _4356 _4359).
Proof. exact (MK_COMB (@lem218090 _4357) (@lem218089 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218092 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term251 _4357 _4358 _4356 _4359) = (term111 _4357 _4358 _4356 _4359).
Proof. exact (TRANS (@lem218086 _4357 _4358 _4356 _4359) (@lem218091 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem218094 (_4357 : nat) (_4358 : nat) (_4356 : nat) (_4359 : nat) : (term255 _4357 _4358 _4356 _4359) = (term256 _4357 _4358 _4356 _4359).
Proof. exact (MK_COMB (@lem218093) (@lem218092 _4357 _4358 _4356 _4359)). Qed.
Lemma lem218095 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) : (term106 _4358 _4359 _4356 _4357) = (term106 _4358 _4359 _4356 _4357).
Proof. exact (eq_refl (term106 _4358 _4359 _4356 _4357)). Qed.
Lemma lem218096 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) : (term250 _4358 _4359 _4356 _4357) = (term89 _4358 _4359 _4356 _4357).
Proof. exact (MK_COMB (@lem218094 _4357 _4358 _4356 _4359) (@lem218095 _4358 _4359 _4356 _4357)). Qed.
Lemma lem218097 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) : (term247 _4357 _4358 _4356 _4359) = (term89 _4358 _4359 _4356 _4357).
Proof. exact (TRANS (@lem218083 _4358 _4359 _4356 _4357) (@lem218096 _4358 _4359 _4356 _4357)). Qed.
Lemma lem218099 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term51) (h2 : term9 d) (h3 : term44 a b c d) : term111 d a c b.
Proof. exact (conj (@lem217741 d h2) (@lem218002 a b c d h1 h3)). Qed.
Lemma lem218101 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) (h1 : term97) : term89 _4358 _4359 _4356 _4357.
Proof. exact (EQ_MP (@lem218097 _4358 _4359 _4356 _4357) (@lem218080 _4357 _4358 _4356 _4359 h1)). Qed.
Lemma lem218102 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) : term89 a b c d.
Proof. exact (@lem218101 a b c d h1). Qed.
Lemma lem218105 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term51) (h3 : term9 d) (h4 : term44 a b c d) : term106 a b c d.
Proof. exact (@lem218102 a b c d h1 (@lem218099 a b c d h2 h3 h4)). Qed.
Lemma lem218106 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term51) (h3 : term9 d) (h4 : term44 a b c d) : term257 a b c d.
Proof. exact (fun h0 : term258 a b c d => @lem218105 a b c d h1 h2 h3 h4). Qed.
Lemma lem218108 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem218109 (a : nat) (b : nat) (c : nat) (d : nat) : (term257 a b c d) = (term106 a b c d).
Proof. exact (@lem218108 (term106 a b c d)). Qed.
Lemma lem218110 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term51) (h3 : term9 d) (h4 : term44 a b c d) : term106 a b c d.
Proof. exact (EQ_MP (@lem218109 a b c d) (@lem218106 a b c d h1 h2 h3 h4)). Qed.
Lemma lem218112 (b : nat) (h1 : term9 b) : term9 b.
Proof. exact (h1). Qed.
Lemma lem218113 (b : nat) (h1 : term9 b) : term198 b.
Proof. exact (fun h0 : b = (NUMERAL 0) => @lem218112 b h1). Qed.
Lemma lem218115 (p : Prop) : (term199 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem218116 (b : nat) : (term198 b) = (term9 b).
Proof. exact (@lem218115 (b = (NUMERAL 0))). Qed.
Lemma lem218117 (b : nat) (h1 : term9 b) : term9 b.
Proof. exact (EQ_MP (@lem218116 b) (@lem218113 b h1)). Qed.
Lemma lem218119 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term24 b c a d.
Proof. exact (proj1 (@lem217445 a b c d h1)). Qed.
Lemma lem218120 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term205 b c a d.
Proof. exact (fun h0 : term100 b c a d => @lem218119 a b c d h1). Qed.
Lemma lem218122 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem218123 (b : nat) (c : nat) (a : nat) (d : nat) : (term205 b c a d) = (term24 b c a d).
Proof. exact (@lem218122 (term24 b c a d)). Qed.
Lemma lem218124 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term24 b c a d.
Proof. exact (EQ_MP (@lem218123 b c a d) (@lem218120 a b c d h1)). Qed.
Lemma lem218125 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term44 a b c d) : term111 b c a d.
Proof. exact (conj (@lem218117 b h1) (@lem218124 a b c d h2)). Qed.
Lemma lem218127 (_4358 : nat) (_4359 : nat) (_4356 : nat) (_4357 : nat) (h1 : term97) : term89 _4358 _4359 _4356 _4357.
Proof. exact (EQ_MP (@lem218097 _4358 _4359 _4356 _4357) (@lem218080 _4357 _4358 _4356 _4359 h1)). Qed.
Lemma lem218128 (c : nat) (d : nat) (a : nat) (b : nat) (h1 : term97) : term89 c d a b.
Proof. exact (@lem218127 c d a b h1). Qed.
Lemma lem218131 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term9 b) (h3 : term44 a b c d) : term106 c d a b.
Proof. exact (@lem218128 c d a b h1 (@lem218125 a b c d h2 h3)). Qed.
Lemma lem218132 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term9 b) (h3 : term44 a b c d) : term257 c d a b.
Proof. exact (fun h0 : term258 c d a b => @lem218131 a b c d h1 h2 h3). Qed.
Lemma lem218134 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem218135 (c : nat) (d : nat) (a : nat) (b : nat) : (term257 c d a b) = (term106 c d a b).
Proof. exact (@lem218134 (term106 c d a b)). Qed.
Lemma lem218136 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term9 b) (h3 : term44 a b c d) : term106 c d a b.
Proof. exact (EQ_MP (@lem218135 c d a b) (@lem218132 a b c d h1 h2 h3)). Qed.
Lemma lem218152 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem218153 (_4365 : nat) (_4364 : nat) : (term259 _4364 _4365) = (term260 _4365 _4364).
Proof. exact (@lem218152 (_4364 = _4365) (term188 _4365 _4364)). Qed.
Lemma lem218161 (_4364 : nat) (_4365 : nat) : (term261 _4364 _4365) = (term261 _4364 _4365).
Proof. exact (eq_refl (term261 _4364 _4365)). Qed.
Lemma lem218162 (_4365 : nat) (_4364 : nat) : (term187 _4364 _4365) = (term262 _4365 _4364).
Proof. exact (MK_COMB (@lem218161 _4364 _4365) (@lem218153 _4365 _4364)). Qed.
Lemma lem218166 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem218167 (_4365 : nat) (_4364 : nat) : (term262 _4365 _4364) = (term263 _4365 _4364).
Proof. exact (@lem218166 (_4364 = _4365) (term188 _4364 _4365) (term188 _4365 _4364)). Qed.
Lemma lem218185 (_4365 : nat) (_4364 : nat) : (term187 _4364 _4365) = (term263 _4365 _4364).
Proof. exact (TRANS (@lem218162 _4365 _4364) (@lem218167 _4365 _4364)). Qed.
Lemma lem218186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem218187 (_4365 : nat) (_4364 : nat) : (term264 _4364 _4365) = (term265 _4365 _4364).
Proof. exact (MK_COMB (@lem218186) (@lem218185 _4365 _4364)). Qed.
Lemma lem218205 (_4365 : nat) (_4364 : nat) : (term263 _4365 _4364) = (term263 _4365 _4364).
Proof. exact (eq_refl (term263 _4365 _4364)). Qed.
Lemma lem218206 (_4365 : nat) (_4364 : nat) : ((term187 _4364 _4365) = (term263 _4365 _4364)) = ((term263 _4365 _4364) = (term263 _4365 _4364)).
Proof. exact (MK_COMB (@lem218187 _4365 _4364) (@lem218205 _4365 _4364)). Qed.
Lemma lem218208 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem218209 (x : Prop) : (x = x) = True.
Proof. exact (@lem218208 Prop x). Qed.
Lemma lem218210 (_4365 : nat) (_4364 : nat) : ((term263 _4365 _4364) = (term263 _4365 _4364)) = True.
Proof. exact (@lem218209 (term263 _4365 _4364)). Qed.
Lemma lem218211 (_4365 : nat) (_4364 : nat) : ((term187 _4364 _4365) = (term263 _4365 _4364)) = True.
Proof. exact (TRANS (@lem218206 _4365 _4364) (@lem218210 _4365 _4364)). Qed.
Lemma lem218212 (_4365 : nat) (_4364 : nat) : True = ((term187 _4364 _4365) = (term263 _4365 _4364)).
Proof. exact (SYM (@lem218211 _4365 _4364)). Qed.
Lemma lem218213 (_4365 : nat) (_4364 : nat) : (term187 _4364 _4365) = (term263 _4365 _4364).
Proof. exact (EQ_MP (@lem218212 _4365 _4364) (@lem0)). Qed.
Lemma lem218214 (_4365 : nat) (_4364 : nat) (h1 : term88) : term263 _4365 _4364.
Proof. exact (EQ_MP (@lem218213 _4365 _4364) (@lem217615 _4364 _4365 h1)). Qed.
Lemma lem218216 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem218217 (_4364 : nat) (_4365 : nat) : (term263 _4365 _4364) = (term266 _4364 _4365).
Proof. exact (@lem218216 (term121 _4365 _4364) (_4364 = _4365)). Qed.
Lemma lem218219 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem218220 (_4365 : nat) (_4364 : nat) : (term267 _4365 _4364) = (term268 _4365 _4364).
Proof. exact (@lem218219 (term188 _4364 _4365) (term188 _4365 _4364)). Qed.
Lemma lem218222 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem218223 (_4364 : nat) (_4365 : nat) : (term269 _4364 _4365) = (Peano.le _4364 _4365).
Proof. exact (@lem218222 (Peano.le _4364 _4365)). Qed.
Lemma lem218224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem218225 (_4364 : nat) (_4365 : nat) : (term270 _4364 _4365) = (term271 _4364 _4365).
Proof. exact (MK_COMB (@lem218224) (@lem218223 _4364 _4365)). Qed.
Lemma lem218227 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem218228 (_4365 : nat) (_4364 : nat) : (term269 _4365 _4364) = (Peano.le _4365 _4364).
Proof. exact (@lem218227 (Peano.le _4365 _4364)). Qed.
Lemma lem218229 (_4365 : nat) (_4364 : nat) : (term268 _4365 _4364) = (term84 _4365 _4364).
Proof. exact (MK_COMB (@lem218225 _4364 _4365) (@lem218228 _4365 _4364)). Qed.
Lemma lem218230 (_4365 : nat) (_4364 : nat) : (term267 _4365 _4364) = (term84 _4365 _4364).
Proof. exact (TRANS (@lem218220 _4365 _4364) (@lem218229 _4365 _4364)). Qed.
Lemma lem218231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem218232 (_4365 : nat) (_4364 : nat) : (term272 _4365 _4364) = (term273 _4365 _4364).
Proof. exact (MK_COMB (@lem218231) (@lem218230 _4365 _4364)). Qed.
Lemma lem218233 (_4364 : nat) (_4365 : nat) : (_4364 = _4365) = (_4364 = _4365).
Proof. exact (eq_refl (_4364 = _4365)). Qed.
Lemma lem218234 (_4364 : nat) (_4365 : nat) : (term266 _4364 _4365) = (term274 _4364 _4365).
Proof. exact (MK_COMB (@lem218232 _4365 _4364) (@lem218233 _4364 _4365)). Qed.
Lemma lem218235 (_4364 : nat) (_4365 : nat) : (term263 _4365 _4364) = (term274 _4364 _4365).
Proof. exact (TRANS (@lem218217 _4364 _4365) (@lem218234 _4364 _4365)). Qed.
Lemma lem218237 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term51) (h3 : term9 b) (h4 : term9 d) (h5 : term44 a b c d) : term275 c d a b.
Proof. exact (conj (@lem218110 a b c d h1 h2 h4 h5) (@lem218136 a b c d h1 h3 h5)). Qed.
Lemma lem218239 (_4364 : nat) (_4365 : nat) (h1 : term88) : term274 _4364 _4365.
Proof. exact (EQ_MP (@lem218235 _4364 _4365) (@lem218214 _4365 _4364 h1)). Qed.
Lemma lem218240 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term88) : term276 a b c d.
Proof. exact (@lem218239 (Nat.div a b) (Nat.div c d) h1). Qed.
Lemma lem218243 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (Nat.div a b) = (Nat.div c d).
Proof. exact (@lem218240 a b c d h2 (@lem218237 a b c d h1 h3 h4 h5 h6)). Qed.
Lemma lem218244 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : term277 a b c d.
Proof. exact (fun h0 : term189 a b c d => @lem218243 a b c d h1 h2 h3 h4 h5 h6). Qed.
Lemma lem218246 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem218247 (a : nat) (b : nat) (c : nat) (d : nat) : (term277 a b c d) = ((Nat.div a b) = (Nat.div c d)).
Proof. exact (@lem218246 ((Nat.div a b) = (Nat.div c d))). Qed.
Lemma lem218248 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (Nat.div a b) = (Nat.div c d).
Proof. exact (EQ_MP (@lem218247 a b c d) (@lem218244 a b c d h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem218251 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem218253 (a : nat) (b : nat) (c : nat) (d : nat) : (term189 a b c d) = (term278 a b c d).
Proof. exact (@lem218251 ((Nat.div a b) = (Nat.div c d))). Qed.
Lemma lem218256 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term44 a b c d) : term278 a b c d.
Proof. exact (EQ_MP (@lem218253 a b c d) (@lem217617 a b c d h1)). Qed.
Lemma lem218259 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (@lem218256 a b c d h6 (@lem218248 a b c d h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem218260 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : term279.
Proof. exact (fun h0 : ~ False => @lem218259 a b c d h1 h2 h3 h4 h5 h6). Qed.
Lemma lem218262 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem218263 : term279 = False.
Proof. exact (@lem218262 False). Qed.
Lemma lem218264 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218263) (@lem218260 a b c d h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem218265 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 d) = False.
Proof. exact (prop_ext (fun h7 : term9 d => @lem218264 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217589 d h5)). Qed.
Lemma lem218266 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218265 a b c d h1 h2 h3 h4 h5 h6) (@lem217589 d h5)). Qed.
Lemma lem218267 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 b) = False.
Proof. exact (prop_ext (fun h7 : term9 b => @lem218266 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217587 b h4)). Qed.
Lemma lem218268 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218267 a b c d h1 h2 h3 h4 h5 h6) (@lem217587 b h4)). Qed.
Lemma lem218269 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 d) = False.
Proof. exact (prop_ext (fun h7 : term9 d => @lem218268 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217455 d h5)). Qed.
Lemma lem218270 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218269 a b c d h1 h2 h3 h4 h5 h6) (@lem217455 d h5)). Qed.
Lemma lem218271 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 b) = False.
Proof. exact (prop_ext (fun h7 : term9 b => @lem218270 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217451 b h4)). Qed.
Lemma lem218272 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218271 a b c d h1 h2 h3 h4 h5 h6) (@lem217451 b h4)). Qed.
Lemma lem218273 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : term51 = False.
Proof. exact (prop_ext (fun h7 : term51 => @lem218272 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217493 h3)). Qed.
Lemma lem218274 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218273 a b c d h1 h2 h3 h4 h5 h6) (@lem217493 h3)). Qed.
Lemma lem218275 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 d) = False.
Proof. exact (prop_ext (fun h7 : term9 d => @lem218274 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217455 d h5)). Qed.
Lemma lem218276 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218275 a b c d h1 h2 h3 h4 h5 h6) (@lem217455 d h5)). Qed.
Lemma lem218277 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 b) = False.
Proof. exact (prop_ext (fun h7 : term9 b => @lem218276 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217451 b h4)). Qed.
Lemma lem218278 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218277 a b c d h1 h2 h3 h4 h5 h6) (@lem217451 b h4)). Qed.
Lemma lem218279 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : term51 = False.
Proof. exact (prop_ext (fun h7 : term51 => @lem218278 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217441 h3)). Qed.
Lemma lem218280 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218279 a b c d h1 h2 h3 h4 h5 h6) (@lem217441 h3)). Qed.
Lemma lem218281 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 d) = False.
Proof. exact (prop_ext (fun h7 : term9 d => @lem218280 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217231 d h5)). Qed.
Lemma lem218282 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218281 a b c d h1 h2 h3 h4 h5 h6) (@lem217231 d h5)). Qed.
Lemma lem218283 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 b) = False.
Proof. exact (prop_ext (fun h7 : term9 b => @lem218282 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217221 b h4)). Qed.
Lemma lem218284 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218283 a b c d h1 h2 h3 h4 h5 h6) (@lem217221 b h4)). Qed.
Lemma lem218285 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : term51 = False.
Proof. exact (prop_ext (fun h7 : term51 => @lem218284 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem217211 h3)). Qed.
Lemma lem218286 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218285 a b c d h1 h2 h3 h4 h5 h6) (@lem217211 h3)). Qed.
Lemma lem218287 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 d) = False.
Proof. exact (prop_ext (fun h7 : term9 d => @lem218286 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem216786 d h5)). Qed.
Lemma lem218288 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218287 a b c d h1 h2 h3 h4 h5 h6) (@lem216786 d h5)). Qed.
Lemma lem218289 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : (term9 b) = False.
Proof. exact (prop_ext (fun h7 : term9 b => @lem218288 a b c d h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem216780 b h4)). Qed.
Lemma lem218290 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term51) (h4 : term9 b) (h5 : term9 d) (h6 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218289 a b c d h1 h2 h3 h4 h5 h6) (@lem216780 b h4)). Qed.
Lemma lem218291 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term9 b) (h4 : term9 d) (h5 : term44 a b c d) : term49.
Proof. exact (fun h0 : term51 => @lem218290 a b c d h1 h2 h0 h3 h4 h5). Qed.
Lemma lem218292 : term49 = term50.
Proof. exact (@lem69 term51). Qed.
Lemma lem218293 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term88) (h3 : term9 b) (h4 : term9 d) (h5 : term44 a b c d) : term50.
Proof. exact (EQ_MP (@lem218292) (@lem218291 a b c d h1 h2 h3 h4 h5)). Qed.
Lemma lem218294 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term97) (h2 : term9 b) (h3 : term9 d) (h4 : term44 a b c d) : term54.
Proof. exact (fun h0 : term88 => @lem218293 a b c d h1 h0 h2 h3 h4). Qed.
Lemma lem218295 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) (h3 : term44 a b c d) : term57.
Proof. exact (fun h0 : term97 => @lem218294 a b c d h0 h1 h2 h3). Qed.
Lemma lem218296 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) : term60 a b c d.
Proof. exact (fun h0 : term44 a b c d => @lem218295 a b c d h1 h2 h0). Qed.
Lemma lem218297 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : term9 b) : term63 a b c d.
Proof. exact (fun h0 : term9 d => @lem218296 a c b d h1 h0). Qed.
Lemma lem218298 (a : nat) (b : nat) (c : nat) (d : nat) : term64 a b c d.
Proof. exact (fun h0 : term9 b => @lem218297 a c d b h0). Qed.
Lemma lem218303 (b : nat) (c : nat) (d : nat) : term68 b c d.
Proof. exact (fun a : nat => @lem218298 a b c d). Qed.
Lemma lem218308 (c : nat) (d : nat) : term72 c d.
Proof. exact (fun b : nat => @lem218303 b c d). Qed.
Lemma lem218313 (d : nat) : term76 d.
Proof. exact (fun c : nat => @lem218308 c d). Qed.
Lemma lem218318 : term80.
Proof. exact (fun d : nat => @lem218313 d). Qed.
Lemma lem218319 : term79.
Proof. exact (EQ_MP (@lem216768) (@lem218318)). Qed.
Lemma lem218320 (d : nat) : term280 d.
Proof. exact (@lem218319 d). Qed.
Lemma lem218321 (d : nat) : (term280 d) = (term75 d).
Proof. exact (eq_refl (term280 d)). Qed.
Lemma lem218322 (d : nat) : term75 d.
Proof. exact (EQ_MP (@lem218321 d) (@lem218320 d)). Qed.
Lemma lem218323 (d : nat) (c : nat) : term281 d c.
Proof. exact (@lem218322 d c). Qed.
Lemma lem218324 (c : nat) (d : nat) : (term281 d c) = (term71 c d).
Proof. exact (eq_refl (term281 d c)). Qed.
Lemma lem218325 (c : nat) (d : nat) : term71 c d.
Proof. exact (EQ_MP (@lem218324 c d) (@lem218323 d c)). Qed.
Lemma lem218326 (c : nat) (d : nat) (b : nat) : term282 c d b.
Proof. exact (@lem218325 c d b). Qed.
Lemma lem218327 (b : nat) (c : nat) (d : nat) : (term282 c d b) = (term67 b c d).
Proof. exact (eq_refl (term282 c d b)). Qed.
Lemma lem218328 (b : nat) (c : nat) (d : nat) : term67 b c d.
Proof. exact (EQ_MP (@lem218327 b c d) (@lem218326 c d b)). Qed.
Lemma lem218329 (b : nat) (c : nat) (d : nat) (a : nat) : term283 b c d a.
Proof. exact (@lem218328 b c d a). Qed.
Lemma lem218330 (a : nat) (b : nat) (c : nat) (d : nat) : (term283 b c d a) = (term45 a b c d).
Proof. exact (eq_refl (term283 b c d a)). Qed.
Lemma lem218331 (a : nat) (b : nat) (c : nat) (d : nat) : term45 a b c d.
Proof. exact (EQ_MP (@lem218330 a b c d) (@lem218329 b c d a)). Qed.
Lemma lem218333 (a : nat) (b : nat) (c : nat) (d : nat) : term45 a b c d.
Proof. exact (@lem216458 a b c d (@lem218331 a b c d)). Qed.
Lemma lem218334 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : term9 b) : term62 a b c d.
Proof. exact (@lem218333 a b c d (@lem216074 b h1)). Qed.
Lemma lem218335 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) : term59 a b c d.
Proof. exact (@lem218334 a c d b h1 (@lem216069 d h2)). Qed.
Lemma lem218336 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) (h3 : term44 a b c d) : term56.
Proof. exact (@lem218335 a c b d h1 h2 (@lem216443 a b c d h3)). Qed.
Lemma lem218337 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) (h3 : term44 a b c d) : term53.
Proof. exact (@lem218336 a b c d h1 h2 h3 (@lem216054)). Qed.
Lemma lem218338 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) (h3 : term44 a b c d) : term49.
Proof. exact (@lem218337 a b c d h1 h2 h3 (@lem92426)). Qed.
Lemma lem218339 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) (h3 : term44 a b c d) : False.
Proof. exact (@lem218338 a b c d h1 h2 h3 (@lem81820)). Qed.
Lemma lem218340 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) (h3 : term44 a b c d) : (term44 a b c d) = False.
Proof. exact (prop_ext (fun h4 : term44 a b c d => @lem218339 a b c d h1 h2 h3) (fun h4 : False => @lem216443 a b c d h3)). Qed.
Lemma lem218341 (a : nat) (b : nat) (c : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) (h3 : term44 a b c d) : False.
Proof. exact (EQ_MP (@lem218340 a b c d h1 h2 h3) (@lem216443 a b c d h3)). Qed.
Lemma lem218342 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) : term43 a b c d.
Proof. exact (fun h0 : term44 a b c d => @lem218341 a b c d h1 h2 h0). Qed.
Lemma lem218344 (a : nat) (c : nat) (b : nat) (d : nat) (h1 : term9 b) (h2 : term9 d) : term38 a b c d.
Proof. exact (EQ_MP (@lem216442 a b c d) (@lem218342 a c b d h1 h2)). Qed.
Lemma lem218346 (a : nat) (c : nat) (d : nat) (b : nat) (h1 : term9 b) : term38 a b c d.
Proof. exact (or_elim (@lem216067 d) (fun h0 : d = (NUMERAL 0) => @lem216359 a b c d h0) (fun h0 : term9 d => @lem218344 a c b d h1 h0)). Qed.
Lemma lem218347 (a : nat) (b : nat) (c : nat) (d : nat) : term38 a b c d.
Proof. exact (or_elim (@lem216072 b) (fun h0 : b = (NUMERAL 0) => @lem216179 a c d b h0) (fun h0 : term9 b => @lem218346 a c d b h0)). Qed.
Lemma lem218352 (a : nat) (b : nat) (c : nat) : term284 a b c.
Proof. exact (fun d : nat => @lem218347 a b c d). Qed.
Lemma lem218357 (a : nat) (b : nat) : term285 a b.
Proof. exact (fun c : nat => @lem218352 a b c). Qed.
Lemma lem218362 (a : nat) : term286 a.
Proof. exact (fun b : nat => @lem218357 a b). Qed.
Lemma lem218367 : term287.
Proof. exact (fun a : nat => @lem218362 a). Qed.
