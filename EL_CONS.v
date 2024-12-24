Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EL_CONS_term_abbrevs.
Require Import NOT_SUC_spec.
Require Import SUC_SUB1_spec.
Require Import thm0_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm12653_spec.
Require Import thm15249_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem1206101 (n : nat) : term0 n.
Proof. exact (@lem137156 n). Qed.
Lemma lem1206102 (n : nat) : (term0 n) = ((term1 n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1206104 (n : nat) : term2 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1206105 (n : nat) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1206106 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem1206105 n) (@lem1206104 n)). Qed.
Lemma lem1206107 (n : nat) : term4 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1206123 (P : nat -> Prop) : term5 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1206124 {_28249 : Type'} : term6 _28249.
Proof. exact (@lem1206123 (term7 _28249)). Qed.
Lemma lem1206125 {_28249 : Type'} : (term8 _28249) = (term9 _28249).
Proof. exact (eq_refl (term8 _28249)). Qed.
Lemma lem1206126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1206127 {_28249 : Type'} : (term10 _28249) = (term11 _28249).
Proof. exact (MK_COMB (@lem1206126) (@lem1206125 _28249)). Qed.
Lemma lem1206128 {_28249 : Type'} (n : nat) : (term12 _28249 n) = (term13 _28249 n).
Proof. exact (eq_refl (term12 _28249 n)). Qed.
Lemma lem1206129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206130 {_28249 : Type'} (n : nat) : (term14 _28249 n) = (term15 _28249 n).
Proof. exact (MK_COMB (@lem1206129) (@lem1206128 _28249 n)). Qed.
Lemma lem1206131 {_28249 : Type'} (n : nat) : (term16 _28249 n) = (term17 _28249 n).
Proof. exact (eq_refl (term16 _28249 n)). Qed.
Lemma lem1206132 {_28249 : Type'} (n : nat) : (term18 _28249 n) = (term19 _28249 n).
Proof. exact (MK_COMB (@lem1206130 _28249 n) (@lem1206131 _28249 n)). Qed.
Lemma lem1206133 {_28249 : Type'} : (term20 _28249) = (term21 _28249).
Proof. exact (fun_ext (fun n : nat => @lem1206132 _28249 n)). Qed.
Lemma lem1206134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1206135 {_28249 : Type'} : (term22 _28249) = (term23 _28249).
Proof. exact (MK_COMB (@lem1206134) (@lem1206133 _28249)). Qed.
Lemma lem1206136 {_28249 : Type'} : (term24 _28249) = (term25 _28249).
Proof. exact (MK_COMB (@lem1206127 _28249) (@lem1206135 _28249)). Qed.
Lemma lem1206137 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1206138 {_28249 : Type'} : (term26 _28249) = (term27 _28249).
Proof. exact (MK_COMB (@lem1206137) (@lem1206136 _28249)). Qed.
Lemma lem1206139 {_28249 : Type'} (n : nat) : (term12 _28249 n) = (term13 _28249 n).
Proof. exact (eq_refl (term12 _28249 n)). Qed.
Lemma lem1206140 {_28249 : Type'} : (term28 _28249) = (term7 _28249).
Proof. exact (fun_ext (fun n : nat => @lem1206139 _28249 n)). Qed.
Lemma lem1206141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1206142 {_28249 : Type'} : (term29 _28249) = (term30 _28249).
Proof. exact (MK_COMB (@lem1206141) (@lem1206140 _28249)). Qed.
Lemma lem1206143 {_28249 : Type'} : (term6 _28249) = (term31 _28249).
Proof. exact (MK_COMB (@lem1206138 _28249) (@lem1206142 _28249)). Qed.
Lemma lem1206144 {_28249 : Type'} : term31 _28249.
Proof. exact (EQ_MP (@lem1206143 _28249) (@lem1206124 _28249)). Qed.
Lemma lem1206157 {_25569 : Type'} (l : list _25569) : (term32 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1206158 {_28249 : Type'} (l : list _28249) : (term32 _28249 l) = (@hd _28249 l).
Proof. exact (@lem1206157 _28249 l). Qed.
Lemma lem1206159 {_28249 : Type'} (h : _28249) (t : list _28249) : (term33 _28249 h t) = (term34 _28249 h t).
Proof. exact (@lem1206158 _28249 (@cons _28249 h t)). Qed.
Lemma lem1206161 {A : Type'} (t : list A) (h : A) : (term34 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1206162 {_28249 : Type'} (t : list _28249) (h : _28249) : (term34 _28249 h t) = h.
Proof. exact (@lem1206161 _28249 t h). Qed.
Lemma lem1206163 {_28249 : Type'} (t : list _28249) (h : _28249) : (term33 _28249 h t) = h.
Proof. exact (TRANS (@lem1206159 _28249 h t) (@lem1206162 _28249 t h)). Qed.
Lemma lem1206164 {_28249 : Type'} : (@eq _28249) = (@eq _28249).
Proof. exact (eq_refl (@eq _28249)). Qed.
Lemma lem1206165 {_28249 : Type'} (t : list _28249) (h : _28249) : (term35 _28249 h t) = (@eq _28249 h).
Proof. exact (MK_COMB (@lem1206164 _28249) (@lem1206163 _28249 t h)). Qed.
Lemma lem1206167 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term36 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem1206168 {_28249 : Type'} (x : nat) (z : _28249) (y : _28249) : (term37 _28249 x y z) = y.
Proof. exact (@lem1206167 _28249 nat x z y). Qed.
Lemma lem1206169 {_28249 : Type'} (t : list _28249) (h : _28249) : (term38 _28249 h t) = h.
Proof. exact (@lem1206168 _28249 (NUMERAL 0) (term39 _28249 t) h). Qed.
Lemma lem1206170 {_28249 : Type'} (t : list _28249) (h : _28249) : ((term33 _28249 h t) = (term38 _28249 h t)) = (h = h).
Proof. exact (MK_COMB (@lem1206165 _28249 t h) (@lem1206169 _28249 t h)). Qed.
Lemma lem1206172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206173 {_28249 : Type'} (x : _28249) : (x = x) = True.
Proof. exact (@lem1206172 _28249 x). Qed.
Lemma lem1206174 {_28249 : Type'} (h : _28249) : (h = h) = True.
Proof. exact (@lem1206173 _28249 h). Qed.
Lemma lem1206175 {_28249 : Type'} (h : _28249) (t : list _28249) : ((term33 _28249 h t) = (term38 _28249 h t)) = True.
Proof. exact (TRANS (@lem1206170 _28249 t h) (@lem1206174 _28249 h)). Qed.
Lemma lem1206176 {_28249 : Type'} (h : _28249) : (term40 _28249 h) = (term41 _28249).
Proof. exact (fun_ext (fun t : list _28249 => @lem1206175 _28249 h t)). Qed.
Lemma lem1206177 {_28249 : Type'} : (@all (list _28249)) = (@all (list _28249)).
Proof. exact (eq_refl (@all (list _28249))). Qed.
Lemma lem1206178 {_28249 : Type'} (h : _28249) : (term42 _28249 h) = (term43 _28249).
Proof. exact (MK_COMB (@lem1206177 _28249) (@lem1206176 _28249 h)). Qed.
Lemma lem1206180 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206181 {_28249 : Type'} (t : Prop) : (term45 _28249 t) = t.
Proof. exact (@lem1206180 (list _28249) t). Qed.
Lemma lem1206182 {_28249 : Type'} : (term43 _28249) = True.
Proof. exact (@lem1206181 _28249 True). Qed.
Lemma lem1206183 {_28249 : Type'} (h : _28249) : (term42 _28249 h) = True.
Proof. exact (TRANS (@lem1206178 _28249 h) (@lem1206182 _28249)). Qed.
Lemma lem1206184 {_28249 : Type'} : (term46 _28249) = (term47 _28249).
Proof. exact (fun_ext (fun h : _28249 => @lem1206183 _28249 h)). Qed.
Lemma lem1206185 {_28249 : Type'} : (@all _28249) = (@all _28249).
Proof. exact (eq_refl (@all _28249)). Qed.
Lemma lem1206186 {_28249 : Type'} : (term9 _28249) = (term48 _28249).
Proof. exact (MK_COMB (@lem1206185 _28249) (@lem1206184 _28249)). Qed.
Lemma lem1206188 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206189 {_28249 : Type'} (t : Prop) : (term44 _28249 t) = t.
Proof. exact (@lem1206188 _28249 t). Qed.
Lemma lem1206190 {_28249 : Type'} : (term48 _28249) = True.
Proof. exact (@lem1206189 _28249 True). Qed.
Lemma lem1206191 {_28249 : Type'} : (term9 _28249) = True.
Proof. exact (TRANS (@lem1206186 _28249) (@lem1206190 _28249)). Qed.
Lemma lem1206192 {_28249 : Type'} : True = (term9 _28249).
Proof. exact (SYM (@lem1206191 _28249)). Qed.
Lemma lem1206193 {_28249 : Type'} : term9 _28249.
Proof. exact (EQ_MP (@lem1206192 _28249) (@lem0)). Qed.
Lemma lem1206205 {_25569 : Type'} (n : nat) (l : list _25569) : (term49 _25569 n l) = (term50 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1206206 {_28249 : Type'} (n : nat) (l : list _28249) : (term49 _28249 n l) = (term50 _28249 n l).
Proof. exact (@lem1206205 _28249 n l). Qed.
Lemma lem1206207 {_28249 : Type'} (n : nat) (h : _28249) (t : list _28249) : (term51 _28249 n h t) = (term52 _28249 n h t).
Proof. exact (@lem1206206 _28249 n (@cons _28249 h t)). Qed.
Lemma lem1206209 {A : Type'} (h : A) (t : list A) : (term53 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1206210 {_28249 : Type'} (h : _28249) (t : list _28249) : (term53 _28249 h t) = t.
Proof. exact (@lem1206209 _28249 h t). Qed.
Lemma lem1206211 {_28249 : Type'} (n : nat) : (@EL _28249 n) = (@EL _28249 n).
Proof. exact (eq_refl (@EL _28249 n)). Qed.
Lemma lem1206212 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term52 _28249 n h t) = (@EL _28249 n t).
Proof. exact (MK_COMB (@lem1206211 _28249 n) (@lem1206210 _28249 h t)). Qed.
Lemma lem1206213 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term51 _28249 n h t) = (@EL _28249 n t).
Proof. exact (TRANS (@lem1206207 _28249 n h t) (@lem1206212 _28249 h n t)). Qed.
Lemma lem1206214 {_28249 : Type'} : (@eq _28249) = (@eq _28249).
Proof. exact (eq_refl (@eq _28249)). Qed.
Lemma lem1206215 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term54 _28249 n h t) = (term55 _28249 n t).
Proof. exact (MK_COMB (@lem1206214 _28249) (@lem1206213 _28249 h n t)). Qed.
Lemma lem1206219 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1206107 n (@lem1206106 n)). Qed.
Lemma lem1206220 {_28249 : Type'} : (@COND _28249) = (@COND _28249).
Proof. exact (eq_refl (@COND _28249)). Qed.
Lemma lem1206221 {_28249 : Type'} (n : nat) : (term56 _28249 n) = (@COND _28249 False).
Proof. exact (MK_COMB (@lem1206220 _28249) (@lem1206219 n)). Qed.
Lemma lem1206222 {_28249 : Type'} (h : _28249) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1206223 {_28249 : Type'} (n : nat) (h : _28249) : (term57 _28249 n h) = (@COND _28249 False h).
Proof. exact (MK_COMB (@lem1206221 _28249 n) (@lem1206222 _28249 h)). Qed.
Lemma lem1206225 (n : nat) : (term1 n) = n.
Proof. exact (EQ_MP (@lem1206102 n) (@lem1206101 n)). Qed.
Lemma lem1206226 {_28249 : Type'} : (@EL _28249) = (@EL _28249).
Proof. exact (eq_refl (@EL _28249)). Qed.
Lemma lem1206227 {_28249 : Type'} (n : nat) : (term58 _28249 n) = (@EL _28249 n).
Proof. exact (MK_COMB (@lem1206226 _28249) (@lem1206225 n)). Qed.
Lemma lem1206228 {_28249 : Type'} (t : list _28249) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1206229 {_28249 : Type'} (n : nat) (t : list _28249) : (term59 _28249 n t) = (@EL _28249 n t).
Proof. exact (MK_COMB (@lem1206227 _28249 n) (@lem1206228 _28249 t)). Qed.
Lemma lem1206230 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term60 _28249 h n t) = (term61 _28249 h n t).
Proof. exact (MK_COMB (@lem1206223 _28249 n h) (@lem1206229 _28249 n t)). Qed.
Lemma lem1206232 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1206233 {_28249 : Type'} (t1 : _28249) (t2 : _28249) : (@COND _28249 False t1 t2) = t2.
Proof. exact (@lem1206232 _28249 t1 t2). Qed.
Lemma lem1206234 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term61 _28249 h n t) = (@EL _28249 n t).
Proof. exact (@lem1206233 _28249 h (@EL _28249 n t)). Qed.
Lemma lem1206235 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : (term60 _28249 h n t) = (@EL _28249 n t).
Proof. exact (TRANS (@lem1206230 _28249 h n t) (@lem1206234 _28249 h n t)). Qed.
Lemma lem1206236 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : ((term51 _28249 n h t) = (term60 _28249 h n t)) = ((@EL _28249 n t) = (@EL _28249 n t)).
Proof. exact (MK_COMB (@lem1206215 _28249 h n t) (@lem1206235 _28249 h n t)). Qed.
Lemma lem1206238 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1206239 {_28249 : Type'} (x : _28249) : (x = x) = True.
Proof. exact (@lem1206238 _28249 x). Qed.
Lemma lem1206240 {_28249 : Type'} (n : nat) (t : list _28249) : ((@EL _28249 n t) = (@EL _28249 n t)) = True.
Proof. exact (@lem1206239 _28249 (@EL _28249 n t)). Qed.
Lemma lem1206241 {_28249 : Type'} (h : _28249) (n : nat) (t : list _28249) : ((term51 _28249 n h t) = (term60 _28249 h n t)) = True.
Proof. exact (TRANS (@lem1206236 _28249 h n t) (@lem1206240 _28249 n t)). Qed.
Lemma lem1206242 {_28249 : Type'} (h : _28249) (n : nat) : (term62 _28249 h n) = (term41 _28249).
Proof. exact (fun_ext (fun t : list _28249 => @lem1206241 _28249 h n t)). Qed.
Lemma lem1206243 {_28249 : Type'} : (@all (list _28249)) = (@all (list _28249)).
Proof. exact (eq_refl (@all (list _28249))). Qed.
Lemma lem1206244 {_28249 : Type'} (h : _28249) (n : nat) : (term63 _28249 h n) = (term43 _28249).
Proof. exact (MK_COMB (@lem1206243 _28249) (@lem1206242 _28249 h n)). Qed.
Lemma lem1206246 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206247 {_28249 : Type'} (t : Prop) : (term45 _28249 t) = t.
Proof. exact (@lem1206246 (list _28249) t). Qed.
Lemma lem1206248 {_28249 : Type'} : (term43 _28249) = True.
Proof. exact (@lem1206247 _28249 True). Qed.
Lemma lem1206249 {_28249 : Type'} (h : _28249) (n : nat) : (term63 _28249 h n) = True.
Proof. exact (TRANS (@lem1206244 _28249 h n) (@lem1206248 _28249)). Qed.
Lemma lem1206250 {_28249 : Type'} (n : nat) : (term64 _28249 n) = (term47 _28249).
Proof. exact (fun_ext (fun h : _28249 => @lem1206249 _28249 h n)). Qed.
Lemma lem1206251 {_28249 : Type'} : (@all _28249) = (@all _28249).
Proof. exact (eq_refl (@all _28249)). Qed.
Lemma lem1206252 {_28249 : Type'} (n : nat) : (term17 _28249 n) = (term48 _28249).
Proof. exact (MK_COMB (@lem1206251 _28249) (@lem1206250 _28249 n)). Qed.
Lemma lem1206254 {A : Type'} (t : Prop) : (term44 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1206255 {_28249 : Type'} (t : Prop) : (term44 _28249 t) = t.
Proof. exact (@lem1206254 _28249 t). Qed.
Lemma lem1206256 {_28249 : Type'} : (term48 _28249) = True.
Proof. exact (@lem1206255 _28249 True). Qed.
Lemma lem1206257 {_28249 : Type'} (n : nat) : (term17 _28249 n) = True.
Proof. exact (TRANS (@lem1206252 _28249 n) (@lem1206256 _28249)). Qed.
Lemma lem1206258 {_28249 : Type'} (n : nat) : True = (term17 _28249 n).
Proof. exact (SYM (@lem1206257 _28249 n)). Qed.
Lemma lem1206259 {_28249 : Type'} (n : nat) : term17 _28249 n.
Proof. exact (EQ_MP (@lem1206258 _28249 n) (@lem0)). Qed.
Lemma lem1206260 {_28249 : Type'} (n : nat) : term19 _28249 n.
Proof. exact (fun h0 : term13 _28249 n => @lem1206259 _28249 n). Qed.
Lemma lem1206265 {_28249 : Type'} : term23 _28249.
Proof. exact (fun n : nat => @lem1206260 _28249 n). Qed.
Lemma lem1206266 {_28249 : Type'} : term25 _28249.
Proof. exact (conj (@lem1206193 _28249) (@lem1206265 _28249)). Qed.
Lemma lem1206267 {_28249 : Type'} : term30 _28249.
Proof. exact (@lem1206144 _28249 (@lem1206266 _28249)). Qed.
