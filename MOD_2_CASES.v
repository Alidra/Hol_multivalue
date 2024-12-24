Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_2_CASES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EVEN_MOD_spec.
Require Import NOT_ODD_spec.
Require Import ODD_MOD_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem202901 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem202902 : term1 = term2.
Proof. exact (@lem202901 term1). Qed.
Lemma lem202903 : term2 = term1.
Proof. exact (SYM (@lem202902)). Qed.
Lemma lem202904 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem202907 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem202908 : term5.
Proof. exact (fun h0 : term4 => @lem202907 h0). Qed.
Lemma lem202909 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem202910 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem202911 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem202909 h2 (@lem202910 h1)). Qed.
Lemma lem202912 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem202911 h1 h0). Qed.
Lemma lem202913 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem202914 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem202912 h1 (@lem202913 h2)). Qed.
Lemma lem202915 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem202914 h0 h1). Qed.
Lemma lem202916 : term7.
Proof. exact (fun h0 : term5 => @lem202915 h0). Qed.
Lemma lem202919 : term5.
Proof. exact (@lem202916 (@lem202908)). Qed.
Lemma lem202939 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem202940 : term8 = term9.
Proof. exact (@lem202939 term10). Qed.
Lemma lem202945 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem202946 : term12 = term13.
Proof. exact (MK_COMB (@lem202945) (@lem202940)). Qed.
Lemma lem202949 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem202950 : term15 = term16.
Proof. exact (MK_COMB (@lem202949) (@lem202946)). Qed.
Lemma lem202953 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem202960 : term4 = term18.
Proof. exact (MK_COMB (@lem202953) (@lem202950)). Qed.
Lemma lem202965 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even n) = ((term19 n) = (NUMERAL 0))) = ((Coq.Arith.PeanoNat.Nat.Even n) = ((term19 n) = (NUMERAL 0))).
Proof. exact (eq_refl ((Coq.Arith.PeanoNat.Nat.Even n) = ((term19 n) = (NUMERAL 0)))). Qed.
Lemma lem202966 : term20 = term20.
Proof. exact (fun_ext (fun n : nat => @lem202965 n)). Qed.
Lemma lem202967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem202968 : term10 = term10.
Proof. exact (MK_COMB (@lem202967) (@lem202966)). Qed.
Lemma lem202969 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem202970 : term9 = term9.
Proof. exact (MK_COMB (@lem202969) (@lem202968)). Qed.
Lemma lem202975 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd n) = ((term19 n) = term21)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = ((term19 n) = term21)).
Proof. exact (eq_refl ((Coq.Arith.PeanoNat.Nat.Odd n) = ((term19 n) = term21))). Qed.
Lemma lem202976 : term22 = term22.
Proof. exact (fun_ext (fun n : nat => @lem202975 n)). Qed.
Lemma lem202977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem202978 : term23 = term23.
Proof. exact (MK_COMB (@lem202977) (@lem202976)). Qed.
Lemma lem202979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem202980 : term11 = term11.
Proof. exact (MK_COMB (@lem202979) (@lem202978)). Qed.
Lemma lem202981 : term13 = term13.
Proof. exact (MK_COMB (@lem202980) (@lem202970)). Qed.
Lemma lem202988 (n : nat) : ((term24 n) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((term24 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl ((term24 n) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem202989 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem202988 n)). Qed.
Lemma lem202990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem202991 : term26 = term26.
Proof. exact (MK_COMB (@lem202990) (@lem202989)). Qed.
Lemma lem202992 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem202993 : term14 = term14.
Proof. exact (MK_COMB (@lem202992) (@lem202991)). Qed.
Lemma lem202994 : term16 = term16.
Proof. exact (MK_COMB (@lem202993) (@lem202981)). Qed.
Lemma lem202998 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = False) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (h1). Qed.
Lemma lem202999 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem203000 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = False) : (term27 n) = (@COND nat False).
Proof. exact (MK_COMB (@lem202999) (@lem202998 n h1)). Qed.
Lemma lem203001 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem203002 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = False) : (term28 n) = term29.
Proof. exact (MK_COMB (@lem203000 n h1) (@lem203001)). Qed.
Lemma lem203003 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem203004 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = False) : (term30 n) = term31.
Proof. exact (MK_COMB (@lem203002 n h1) (@lem203003)). Qed.
Lemma lem203006 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem203007 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem203006 nat t1 t2). Qed.
Lemma lem203008 : term31 = term21.
Proof. exact (@lem203007 (NUMERAL 0) term21). Qed.
Lemma lem203009 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = False) : (term30 n) = term21.
Proof. exact (TRANS (@lem203004 n h1) (@lem203008)). Qed.
Lemma lem203010 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem203011 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = False) : ((term19 n) = (term30 n)) = ((term19 n) = term21).
Proof. exact (MK_COMB (@lem203010 n) (@lem203009 n h1)). Qed.
Lemma lem203014 (n : nat) : term33 n.
Proof. exact (fun h0 : (Coq.Arith.PeanoNat.Nat.Even n) = False => @lem203011 n h0). Qed.
Lemma lem203016 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = True) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (h1). Qed.
Lemma lem203017 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem203018 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = True) : (term27 n) = (@COND nat True).
Proof. exact (MK_COMB (@lem203017) (@lem203016 n h1)). Qed.
Lemma lem203019 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem203020 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = True) : (term28 n) = term34.
Proof. exact (MK_COMB (@lem203018 n h1) (@lem203019)). Qed.
Lemma lem203021 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem203022 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = True) : (term30 n) = term35.
Proof. exact (MK_COMB (@lem203020 n h1) (@lem203021)). Qed.
Lemma lem203024 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem203025 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem203024 nat t2 t1). Qed.
Lemma lem203026 : term35 = (NUMERAL 0).
Proof. exact (@lem203025 term21 (NUMERAL 0)). Qed.
Lemma lem203027 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = True) : (term30 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem203022 n h1) (@lem203026)). Qed.
Lemma lem203028 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem203029 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even n) = True) : ((term19 n) = (term30 n)) = ((term19 n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem203028 n) (@lem203027 n h1)). Qed.
Lemma lem203032 (n : nat) : term36 n.
Proof. exact (fun h0 : (Coq.Arith.PeanoNat.Nat.Even n) = True => @lem203029 n h0). Qed.
Lemma lem203033 (n : nat) : term37 n.
Proof. exact (conj (@lem203014 n) (@lem203032 n)). Qed.
Lemma lem203035 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term38 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem203036 (n : nat) : term39 n.
Proof. exact (@lem203035 ((term19 n) = (term30 n)) ((term19 n) = (NUMERAL 0)) (Coq.Arith.PeanoNat.Nat.Even n) ((term19 n) = term21)). Qed.
Lemma lem203069 (n : nat) : ((term19 n) = (term30 n)) = (term40 n).
Proof. exact (@lem203036 n (@lem203033 n)). Qed.
Lemma lem203070 : term41 = term42.
Proof. exact (fun_ext (fun n : nat => @lem203069 n)). Qed.
Lemma lem203071 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203072 : term1 = term43.
Proof. exact (MK_COMB (@lem203071) (@lem203070)). Qed.
Lemma lem203073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem203074 : term3 = term44.
Proof. exact (MK_COMB (@lem203073) (@lem203072)). Qed.
Lemma lem203075 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem203076 : term17 = term45.
Proof. exact (MK_COMB (@lem203075) (@lem203074)). Qed.
Lemma lem203077 : term18 = term46.
Proof. exact (MK_COMB (@lem203076) (@lem202994)). Qed.
Lemma lem203116 : term4 = term46.
Proof. exact (TRANS (@lem202960) (@lem203077)). Qed.
Lemma lem203117 : term46 = term4.
Proof. exact (SYM (@lem203116)). Qed.
Lemma lem203118 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem203119 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem203120 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem203121 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem203124 (n : nat) : (term47 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem16933 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem203125 (n : nat) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem203126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203127 (n : nat) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem203126) (@lem203124 n)). Qed.
Lemma lem203128 (n : nat) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem203127 n) (@lem203125 n)). Qed.
Lemma lem203129 (n : nat) : (term53 n) = (term51 n).
Proof. exact (@lem17160 (term54 n) ((term19 n) = (NUMERAL 0))). Qed.
Lemma lem203130 (n : nat) : (term53 n) = (term52 n).
Proof. exact (TRANS (@lem203129 n) (@lem203128 n)). Qed.
Lemma lem203137 (n : nat) : (term55 n) = (term56 n).
Proof. exact (@lem17160 (Coq.Arith.PeanoNat.Nat.Even n) ((term19 n) = term21)). Qed.
Lemma lem203138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem203139 (n : nat) : (term57 n) = (term58 n).
Proof. exact (MK_COMB (@lem203138) (@lem203130 n)). Qed.
Lemma lem203140 (n : nat) : (term59 n) = (term60 n).
Proof. exact (MK_COMB (@lem203139 n) (@lem203137 n)). Qed.
Lemma lem203141 (n : nat) : (term61 n) = (term59 n).
Proof. exact (@lem17045 (term62 n) (term63 n)). Qed.
Lemma lem203142 (n : nat) : (term61 n) = (term60 n).
Proof. exact (TRANS (@lem203141 n) (@lem203140 n)). Qed.
Lemma lem203143 (P : nat -> Prop) : (term64 P) = (term65 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem203144 : term44 = term66.
Proof. exact (@lem203143 term42). Qed.
Lemma lem203145 (n : nat) : (term67 n) = (term40 n).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem203146 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem203147 (n : nat) : (term68 n) = (term61 n).
Proof. exact (MK_COMB (@lem203146) (@lem203145 n)). Qed.
Lemma lem203148 (n : nat) : (term68 n) = (term60 n).
Proof. exact (TRANS (@lem203147 n) (@lem203142 n)). Qed.
Lemma lem203149 : term69 = term70.
Proof. exact (fun_ext (fun n : nat => @lem203148 n)). Qed.
Lemma lem203150 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem203151 : term66 = term71.
Proof. exact (MK_COMB (@lem203150) (@lem203149)). Qed.
Lemma lem203152 : term44 = term71.
Proof. exact (TRANS (@lem203144) (@lem203151)). Qed.
Lemma lem203154 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem203155 (P : nat -> Prop) (Q : nat -> Prop) : (term74 P Q) = (term75 P Q).
Proof. exact (@lem203154 nat P Q). Qed.
Lemma lem203156 : term76 = term77.
Proof. exact (@lem203155 term78 term79). Qed.
Lemma lem203157 (n : nat) : (term80 n) = (term52 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem203158 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem203159 (n : nat) : (term81 n) = (term58 n).
Proof. exact (MK_COMB (@lem203158) (@lem203157 n)). Qed.
Lemma lem203160 (n : nat) : (term82 n) = (term56 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem203161 (n : nat) : (term83 n) = (term60 n).
Proof. exact (MK_COMB (@lem203159 n) (@lem203160 n)). Qed.
Lemma lem203162 : term84 = term70.
Proof. exact (fun_ext (fun n : nat => @lem203161 n)). Qed.
Lemma lem203163 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem203164 : term76 = term71.
Proof. exact (MK_COMB (@lem203163) (@lem203162)). Qed.
Lemma lem203165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem203166 : term85 = term86.
Proof. exact (MK_COMB (@lem203165) (@lem203164)). Qed.
Lemma lem203167 (n : nat) : (term80 n) = (term52 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem203168 : term87 = term78.
Proof. exact (fun_ext (fun n : nat => @lem203167 n)). Qed.
Lemma lem203169 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem203170 : term88 = term89.
Proof. exact (MK_COMB (@lem203169) (@lem203168)). Qed.
Lemma lem203171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem203172 : term90 = term91.
Proof. exact (MK_COMB (@lem203171) (@lem203170)). Qed.
Lemma lem203173 (n : nat) : (term82 n) = (term56 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem203174 : term92 = term79.
Proof. exact (fun_ext (fun n : nat => @lem203173 n)). Qed.
Lemma lem203175 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem203176 : term93 = term94.
Proof. exact (MK_COMB (@lem203175) (@lem203174)). Qed.
Lemma lem203177 : term77 = term95.
Proof. exact (MK_COMB (@lem203172) (@lem203176)). Qed.
Lemma lem203178 : (term76 = term77) = (term71 = term95).
Proof. exact (MK_COMB (@lem203166) (@lem203177)). Qed.
Lemma lem203179 : term71 = term95.
Proof. exact (EQ_MP (@lem203178) (@lem203156)). Qed.
Lemma lem203257 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term73 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem203258 (P : nat -> Prop) (Q : nat -> Prop) : (term75 P Q) = (term74 P Q).
Proof. exact (@lem203257 nat P Q). Qed.
Lemma lem203259 : term77 = term76.
Proof. exact (@lem203258 term78 term79). Qed.
Lemma lem203260 (n : nat) : (term80 n) = (term52 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem203261 : term87 = term78.
Proof. exact (fun_ext (fun n : nat => @lem203260 n)). Qed.
Lemma lem203262 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem203263 : term88 = term89.
Proof. exact (MK_COMB (@lem203262) (@lem203261)). Qed.
Lemma lem203264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem203265 : term90 = term91.
Proof. exact (MK_COMB (@lem203264) (@lem203263)). Qed.
Lemma lem203266 (n : nat) : (term82 n) = (term56 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem203267 : term92 = term79.
Proof. exact (fun_ext (fun n : nat => @lem203266 n)). Qed.
Lemma lem203268 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem203269 : term93 = term94.
Proof. exact (MK_COMB (@lem203268) (@lem203267)). Qed.
Lemma lem203270 : term77 = term95.
Proof. exact (MK_COMB (@lem203265) (@lem203269)). Qed.
Lemma lem203271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem203272 : term96 = term97.
Proof. exact (MK_COMB (@lem203271) (@lem203270)). Qed.
Lemma lem203273 (n : nat) : (term80 n) = (term52 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem203274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem203275 (n : nat) : (term81 n) = (term58 n).
Proof. exact (MK_COMB (@lem203274) (@lem203273 n)). Qed.
Lemma lem203276 (n : nat) : (term82 n) = (term56 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem203277 (n : nat) : (term83 n) = (term60 n).
Proof. exact (MK_COMB (@lem203275 n) (@lem203276 n)). Qed.
Lemma lem203278 : term84 = term70.
Proof. exact (fun_ext (fun n : nat => @lem203277 n)). Qed.
Lemma lem203279 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem203280 : term76 = term71.
Proof. exact (MK_COMB (@lem203279) (@lem203278)). Qed.
Lemma lem203281 : (term77 = term76) = (term95 = term71).
Proof. exact (MK_COMB (@lem203272) (@lem203280)). Qed.
Lemma lem203282 : term95 = term71.
Proof. exact (EQ_MP (@lem203281) (@lem203259)). Qed.
Lemma lem203283 : term71 = term71.
Proof. exact (TRANS (@lem203179) (@lem203282)). Qed.
Lemma lem203284 : term44 = term71.
Proof. exact (TRANS (@lem203152) (@lem203283)). Qed.
Lemma lem203285 (h1 : term44) : term71.
Proof. exact (EQ_MP (@lem203284) (@lem203118 h1)). Qed.
Lemma lem203289 (n : nat) : (term98 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem16933 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem203291 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem203292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem203293 (n : nat) : (term99 n) = (term100 n).
Proof. exact (MK_COMB (@lem203292) (@lem203289 n)). Qed.
Lemma lem203294 (n : nat) : (term101 n) = (term102 n).
Proof. exact (MK_COMB (@lem203293 n) (@lem203291 n)). Qed.
Lemma lem203299 (n : nat) : (term103 n) = (term103 n).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem203300 (n : nat) : (term104 n) = (term105 n).
Proof. exact (MK_COMB (@lem203299 n) (@lem203294 n)). Qed.
Lemma lem203301 (n : nat) : ((term24 n) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term104 n).
Proof. exact (@lem17784 (term24 n) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem203302 (n : nat) : ((term24 n) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term105 n).
Proof. exact (TRANS (@lem203301 n) (@lem203300 n)). Qed.
Lemma lem203303 : term25 = term106.
Proof. exact (fun_ext (fun n : nat => @lem203302 n)). Qed.
Lemma lem203304 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203305 : term26 = term107.
Proof. exact (MK_COMB (@lem203304) (@lem203303)). Qed.
Lemma lem203307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem203308 (P : nat -> Prop) (Q : nat -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem203307 nat P Q). Qed.
Lemma lem203309 : term112 = term113.
Proof. exact (@lem203308 term114 term115). Qed.
Lemma lem203310 (n : nat) : (term116 n) = (term117 n).
Proof. exact (eq_refl (term116 n)). Qed.
Lemma lem203311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203312 (n : nat) : (term118 n) = (term103 n).
Proof. exact (MK_COMB (@lem203311) (@lem203310 n)). Qed.
Lemma lem203313 (n : nat) : (term119 n) = (term102 n).
Proof. exact (eq_refl (term119 n)). Qed.
Lemma lem203314 (n : nat) : (term120 n) = (term105 n).
Proof. exact (MK_COMB (@lem203312 n) (@lem203313 n)). Qed.
Lemma lem203315 : term121 = term106.
Proof. exact (fun_ext (fun n : nat => @lem203314 n)). Qed.
Lemma lem203316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203317 : term112 = term107.
Proof. exact (MK_COMB (@lem203316) (@lem203315)). Qed.
Lemma lem203318 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem203319 : term122 = term123.
Proof. exact (MK_COMB (@lem203318) (@lem203317)). Qed.
Lemma lem203320 (n : nat) : (term116 n) = (term117 n).
Proof. exact (eq_refl (term116 n)). Qed.
Lemma lem203321 : term124 = term114.
Proof. exact (fun_ext (fun n : nat => @lem203320 n)). Qed.
Lemma lem203322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203323 : term125 = term126.
Proof. exact (MK_COMB (@lem203322) (@lem203321)). Qed.
Lemma lem203324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203325 : term127 = term128.
Proof. exact (MK_COMB (@lem203324) (@lem203323)). Qed.
Lemma lem203326 (n : nat) : (term119 n) = (term102 n).
Proof. exact (eq_refl (term119 n)). Qed.
Lemma lem203327 : term129 = term115.
Proof. exact (fun_ext (fun n : nat => @lem203326 n)). Qed.
Lemma lem203328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203329 : term130 = term131.
Proof. exact (MK_COMB (@lem203328) (@lem203327)). Qed.
Lemma lem203330 : term113 = term132.
Proof. exact (MK_COMB (@lem203325) (@lem203329)). Qed.
Lemma lem203331 : (term112 = term113) = (term107 = term132).
Proof. exact (MK_COMB (@lem203319) (@lem203330)). Qed.
Lemma lem203394 : term107 = term132.
Proof. exact (EQ_MP (@lem203331) (@lem203309)). Qed.
Lemma lem203395 : term26 = term132.
Proof. exact (TRANS (@lem203305) (@lem203394)). Qed.
Lemma lem203396 (h1 : term26) : term132.
Proof. exact (EQ_MP (@lem203395) (@lem203119 h1)). Qed.
Lemma lem203411 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd n) = ((term19 n) = term21)) = (term133 n).
Proof. exact (@lem17784 (Coq.Arith.PeanoNat.Nat.Odd n) ((term19 n) = term21)). Qed.
Lemma lem203412 : term22 = term134.
Proof. exact (fun_ext (fun n : nat => @lem203411 n)). Qed.
Lemma lem203413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203414 : term23 = term135.
Proof. exact (MK_COMB (@lem203413) (@lem203412)). Qed.
Lemma lem203416 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem203417 (P : nat -> Prop) (Q : nat -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem203416 nat P Q). Qed.
Lemma lem203418 : term136 = term137.
Proof. exact (@lem203417 term138 term139). Qed.
Lemma lem203419 (n : nat) : (term140 n) = (term141 n).
Proof. exact (eq_refl (term140 n)). Qed.
Lemma lem203420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203421 (n : nat) : (term142 n) = (term143 n).
Proof. exact (MK_COMB (@lem203420) (@lem203419 n)). Qed.
Lemma lem203422 (n : nat) : (term144 n) = (term145 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem203423 (n : nat) : (term146 n) = (term133 n).
Proof. exact (MK_COMB (@lem203421 n) (@lem203422 n)). Qed.
Lemma lem203424 : term147 = term134.
Proof. exact (fun_ext (fun n : nat => @lem203423 n)). Qed.
Lemma lem203425 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203426 : term136 = term135.
Proof. exact (MK_COMB (@lem203425) (@lem203424)). Qed.
Lemma lem203427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem203428 : term148 = term149.
Proof. exact (MK_COMB (@lem203427) (@lem203426)). Qed.
Lemma lem203429 (n : nat) : (term140 n) = (term141 n).
Proof. exact (eq_refl (term140 n)). Qed.
Lemma lem203430 : term150 = term138.
Proof. exact (fun_ext (fun n : nat => @lem203429 n)). Qed.
Lemma lem203431 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203432 : term151 = term152.
Proof. exact (MK_COMB (@lem203431) (@lem203430)). Qed.
Lemma lem203433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203434 : term153 = term154.
Proof. exact (MK_COMB (@lem203433) (@lem203432)). Qed.
Lemma lem203435 (n : nat) : (term144 n) = (term145 n).
Proof. exact (eq_refl (term144 n)). Qed.
Lemma lem203436 : term155 = term139.
Proof. exact (fun_ext (fun n : nat => @lem203435 n)). Qed.
Lemma lem203437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203438 : term156 = term157.
Proof. exact (MK_COMB (@lem203437) (@lem203436)). Qed.
Lemma lem203439 : term137 = term158.
Proof. exact (MK_COMB (@lem203434) (@lem203438)). Qed.
Lemma lem203440 : (term136 = term137) = (term135 = term158).
Proof. exact (MK_COMB (@lem203428) (@lem203439)). Qed.
Lemma lem203519 : term135 = term158.
Proof. exact (EQ_MP (@lem203440) (@lem203418)). Qed.
Lemma lem203520 : term23 = term158.
Proof. exact (TRANS (@lem203414) (@lem203519)). Qed.
Lemma lem203521 (h1 : term23) : term158.
Proof. exact (EQ_MP (@lem203520) (@lem203120 h1)). Qed.
Lemma lem203536 (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even n) = ((term19 n) = (NUMERAL 0))) = (term159 n).
Proof. exact (@lem17784 (Coq.Arith.PeanoNat.Nat.Even n) ((term19 n) = (NUMERAL 0))). Qed.
Lemma lem203537 : term20 = term160.
Proof. exact (fun_ext (fun n : nat => @lem203536 n)). Qed.
Lemma lem203538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203539 : term10 = term161.
Proof. exact (MK_COMB (@lem203538) (@lem203537)). Qed.
Lemma lem203541 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem203542 (P : nat -> Prop) (Q : nat -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem203541 nat P Q). Qed.
Lemma lem203543 : term162 = term163.
Proof. exact (@lem203542 term164 term165). Qed.
Lemma lem203544 (n : nat) : (term166 n) = (term167 n).
Proof. exact (eq_refl (term166 n)). Qed.
Lemma lem203545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203546 (n : nat) : (term168 n) = (term169 n).
Proof. exact (MK_COMB (@lem203545) (@lem203544 n)). Qed.
Lemma lem203547 (n : nat) : (term170 n) = (term62 n).
Proof. exact (eq_refl (term170 n)). Qed.
Lemma lem203548 (n : nat) : (term171 n) = (term159 n).
Proof. exact (MK_COMB (@lem203546 n) (@lem203547 n)). Qed.
Lemma lem203549 : term172 = term160.
Proof. exact (fun_ext (fun n : nat => @lem203548 n)). Qed.
Lemma lem203550 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203551 : term162 = term161.
Proof. exact (MK_COMB (@lem203550) (@lem203549)). Qed.
Lemma lem203552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem203553 : term173 = term174.
Proof. exact (MK_COMB (@lem203552) (@lem203551)). Qed.
Lemma lem203554 (n : nat) : (term166 n) = (term167 n).
Proof. exact (eq_refl (term166 n)). Qed.
Lemma lem203555 : term175 = term164.
Proof. exact (fun_ext (fun n : nat => @lem203554 n)). Qed.
Lemma lem203556 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203557 : term176 = term177.
Proof. exact (MK_COMB (@lem203556) (@lem203555)). Qed.
Lemma lem203558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203559 : term178 = term179.
Proof. exact (MK_COMB (@lem203558) (@lem203557)). Qed.
Lemma lem203560 (n : nat) : (term170 n) = (term62 n).
Proof. exact (eq_refl (term170 n)). Qed.
Lemma lem203561 : term180 = term165.
Proof. exact (fun_ext (fun n : nat => @lem203560 n)). Qed.
Lemma lem203562 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203563 : term181 = term182.
Proof. exact (MK_COMB (@lem203562) (@lem203561)). Qed.
Lemma lem203564 : term163 = term183.
Proof. exact (MK_COMB (@lem203559) (@lem203563)). Qed.
Lemma lem203565 : (term162 = term163) = (term161 = term183).
Proof. exact (MK_COMB (@lem203553) (@lem203564)). Qed.
Lemma lem203644 : term161 = term183.
Proof. exact (EQ_MP (@lem203565) (@lem203543)). Qed.
Lemma lem203645 : term10 = term183.
Proof. exact (TRANS (@lem203539) (@lem203644)). Qed.
Lemma lem203646 (h1 : term10) : term183.
Proof. exact (EQ_MP (@lem203645) (@lem203121 h1)). Qed.
Lemma lem203656 (n : nat) : (term102 n) = (term102 n).
Proof. exact (eq_refl (term102 n)). Qed.
Lemma lem203657 : term115 = term115.
Proof. exact (fun_ext (fun n : nat => @lem203656 n)). Qed.
Lemma lem203658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203659 : term131 = term131.
Proof. exact (MK_COMB (@lem203658) (@lem203657)). Qed.
Lemma lem203672 (n : nat) : (term117 n) = (term117 n).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem203673 : term114 = term114.
Proof. exact (fun_ext (fun n : nat => @lem203672 n)). Qed.
Lemma lem203674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203675 : term126 = term126.
Proof. exact (MK_COMB (@lem203674) (@lem203673)). Qed.
Lemma lem203676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203677 : term128 = term128.
Proof. exact (MK_COMB (@lem203676) (@lem203675)). Qed.
Lemma lem203678 : term132 = term132.
Proof. exact (MK_COMB (@lem203677) (@lem203659)). Qed.
Lemma lem203679 (h1 : term26) : term132.
Proof. exact (EQ_MP (@lem203678) (@lem203396 h1)). Qed.
Lemma lem203706 (n : nat) : (term145 n) = (term145 n).
Proof. exact (eq_refl (term145 n)). Qed.
Lemma lem203707 : term139 = term139.
Proof. exact (fun_ext (fun n : nat => @lem203706 n)). Qed.
Lemma lem203708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203709 : term157 = term157.
Proof. exact (MK_COMB (@lem203708) (@lem203707)). Qed.
Lemma lem203736 (n : nat) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem203737 : term138 = term138.
Proof. exact (fun_ext (fun n : nat => @lem203736 n)). Qed.
Lemma lem203738 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203739 : term152 = term152.
Proof. exact (MK_COMB (@lem203738) (@lem203737)). Qed.
Lemma lem203740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203741 : term154 = term154.
Proof. exact (MK_COMB (@lem203740) (@lem203739)). Qed.
Lemma lem203742 : term158 = term158.
Proof. exact (MK_COMB (@lem203741) (@lem203709)). Qed.
Lemma lem203743 (h1 : term23) : term158.
Proof. exact (EQ_MP (@lem203742) (@lem203521 h1)). Qed.
Lemma lem203768 (n : nat) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem203769 : term165 = term165.
Proof. exact (fun_ext (fun n : nat => @lem203768 n)). Qed.
Lemma lem203770 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203771 : term182 = term182.
Proof. exact (MK_COMB (@lem203770) (@lem203769)). Qed.
Lemma lem203796 (n : nat) : (term167 n) = (term167 n).
Proof. exact (eq_refl (term167 n)). Qed.
Lemma lem203797 : term164 = term164.
Proof. exact (fun_ext (fun n : nat => @lem203796 n)). Qed.
Lemma lem203798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203799 : term177 = term177.
Proof. exact (MK_COMB (@lem203798) (@lem203797)). Qed.
Lemma lem203800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem203801 : term179 = term179.
Proof. exact (MK_COMB (@lem203800) (@lem203799)). Qed.
Lemma lem203802 : term183 = term183.
Proof. exact (MK_COMB (@lem203801) (@lem203771)). Qed.
Lemma lem203803 (h1 : term10) : term183.
Proof. exact (EQ_MP (@lem203802) (@lem203646 h1)). Qed.
Lemma lem203861 (n : nat) (h1 : term60 n) : term60 n.
Proof. exact (h1). Qed.
Lemma lem203862 (h1 : term10) : term182.
Proof. exact (proj2 (@lem203803 h1)). Qed.
Lemma lem203864 (h1 : term23) : term157.
Proof. exact (proj2 (@lem203743 h1)). Qed.
Lemma lem203866 (h1 : term26) : term131.
Proof. exact (proj2 (@lem203679 h1)). Qed.
Lemma lem203868 (n : nat) (h1 : term52 n) : term52 n.
Proof. exact (h1). Qed.
Lemma lem203869 (n : nat) (h1 : term56 n) : term56 n.
Proof. exact (h1). Qed.
Lemma lem203894 (n : nat) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem203895 : term165 = term165.
Proof. exact (fun_ext (fun n : nat => @lem203894 n)). Qed.
Lemma lem203896 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem203898 : term182 = term182.
Proof. exact (MK_COMB (@lem203896) (@lem203895)). Qed.
Lemma lem203899 (h1 : term10) : term182.
Proof. exact (EQ_MP (@lem203898) (@lem203862 h1)). Qed.
Lemma lem204006 (n : nat) : (term145 n) = (term145 n).
Proof. exact (eq_refl (term145 n)). Qed.
Lemma lem204007 : term139 = term139.
Proof. exact (fun_ext (fun n : nat => @lem204006 n)). Qed.
Lemma lem204008 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem204010 : term157 = term157.
Proof. exact (MK_COMB (@lem204008) (@lem204007)). Qed.
Lemma lem204011 (h1 : term23) : term157.
Proof. exact (EQ_MP (@lem204010) (@lem203864 h1)). Qed.
Lemma lem204032 (n : nat) : (term102 n) = (term102 n).
Proof. exact (eq_refl (term102 n)). Qed.
Lemma lem204033 : term115 = term115.
Proof. exact (fun_ext (fun n : nat => @lem204032 n)). Qed.
Lemma lem204034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem204036 : term131 = term131.
Proof. exact (MK_COMB (@lem204034) (@lem204033)). Qed.
Lemma lem204037 (h1 : term26) : term131.
Proof. exact (EQ_MP (@lem204036) (@lem203866 h1)). Qed.
Lemma lem204049 (_4144 : nat) (h1 : term10) : term170 _4144.
Proof. exact (@lem203899 h1 _4144). Qed.
Lemma lem204050 (_4144 : nat) : (term170 _4144) = (term62 _4144).
Proof. exact (eq_refl (term170 _4144)). Qed.
Lemma lem204073 (_4152 : nat) (h1 : term23) : term144 _4152.
Proof. exact (@lem204011 h1 _4152). Qed.
Lemma lem204074 (_4152 : nat) : (term144 _4152) = (term145 _4152).
Proof. exact (eq_refl (term144 _4152)). Qed.
Lemma lem204079 (_4154 : nat) (h1 : term26) : term119 _4154.
Proof. exact (@lem204037 h1 _4154). Qed.
Lemma lem204080 (_4154 : nat) : (term119 _4154) = (term102 _4154).
Proof. exact (eq_refl (term119 _4154)). Qed.
Lemma lem204093 (_4144 : nat) (h1 : term10) : term62 _4144.
Proof. exact (EQ_MP (@lem204050 _4144) (@lem204049 _4144 h1)). Qed.
Lemma lem204121 (n : nat) (h1 : term52 n) : term48 n.
Proof. exact (proj2 (@lem203868 n h1)). Qed.
Lemma lem204145 (_4152 : nat) (h1 : term23) : term145 _4152.
Proof. exact (EQ_MP (@lem204074 _4152) (@lem204073 _4152 h1)). Qed.
Lemma lem204157 (_4154 : nat) (h1 : term26) : term102 _4154.
Proof. exact (EQ_MP (@lem204080 _4154) (@lem204079 _4154 h1)). Qed.
Lemma lem204161 (n : nat) (h1 : term56 n) : term184 n.
Proof. exact (proj2 (@lem203869 n h1)). Qed.
Lemma lem204228 (n : nat) (h1 : term52 n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (proj1 (@lem203868 n h1)). Qed.
Lemma lem204229 (n : nat) (h1 : term52 n) : term185 n.
Proof. exact (fun h0 : term54 n => @lem204228 n h1). Qed.
Lemma lem204231 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem204232 (n : nat) : (term185 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem204231 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem204233 (n : nat) (h1 : term52 n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem204232 n) (@lem204229 n h1)). Qed.
Lemma lem204239 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem204240 (_4144 : nat) : (term62 _4144) = (term187 _4144).
Proof. exact (@lem204239 ((term19 _4144) = (NUMERAL 0)) (term54 _4144)). Qed.
Lemma lem204248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem204249 (_4144 : nat) : (term188 _4144) = (term189 _4144).
Proof. exact (MK_COMB (@lem204248) (@lem204240 _4144)). Qed.
Lemma lem204257 (_4144 : nat) : (term187 _4144) = (term187 _4144).
Proof. exact (eq_refl (term187 _4144)). Qed.
Lemma lem204258 (_4144 : nat) : ((term62 _4144) = (term187 _4144)) = ((term187 _4144) = (term187 _4144)).
Proof. exact (MK_COMB (@lem204249 _4144) (@lem204257 _4144)). Qed.
Lemma lem204260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem204261 (x : Prop) : (x = x) = True.
Proof. exact (@lem204260 Prop x). Qed.
Lemma lem204262 (_4144 : nat) : ((term187 _4144) = (term187 _4144)) = True.
Proof. exact (@lem204261 (term187 _4144)). Qed.
Lemma lem204263 (_4144 : nat) : ((term62 _4144) = (term187 _4144)) = True.
Proof. exact (TRANS (@lem204258 _4144) (@lem204262 _4144)). Qed.
Lemma lem204264 (_4144 : nat) : True = ((term62 _4144) = (term187 _4144)).
Proof. exact (SYM (@lem204263 _4144)). Qed.
Lemma lem204265 (_4144 : nat) : (term62 _4144) = (term187 _4144).
Proof. exact (EQ_MP (@lem204264 _4144) (@lem0)). Qed.
Lemma lem204266 (_4144 : nat) (h1 : term10) : term187 _4144.
Proof. exact (EQ_MP (@lem204265 _4144) (@lem204093 _4144 h1)). Qed.
Lemma lem204268 (b : Prop) (a : Prop) : (a \/ b) = (term190 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem204269 (_4144 : nat) : (term187 _4144) = (term191 _4144).
Proof. exact (@lem204268 (term54 _4144) ((term19 _4144) = (NUMERAL 0))). Qed.
Lemma lem204271 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem204272 (_4144 : nat) : (term47 _4144) = (Coq.Arith.PeanoNat.Nat.Even _4144).
Proof. exact (@lem204271 (Coq.Arith.PeanoNat.Nat.Even _4144)). Qed.
Lemma lem204273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem204274 (_4144 : nat) : (term193 _4144) = (term194 _4144).
Proof. exact (MK_COMB (@lem204273) (@lem204272 _4144)). Qed.
Lemma lem204275 (_4144 : nat) : ((term19 _4144) = (NUMERAL 0)) = ((term19 _4144) = (NUMERAL 0)).
Proof. exact (eq_refl ((term19 _4144) = (NUMERAL 0))). Qed.
Lemma lem204276 (_4144 : nat) : (term191 _4144) = (term195 _4144).
Proof. exact (MK_COMB (@lem204274 _4144) (@lem204275 _4144)). Qed.
Lemma lem204277 (_4144 : nat) : (term187 _4144) = (term195 _4144).
Proof. exact (TRANS (@lem204269 _4144) (@lem204276 _4144)). Qed.
Lemma lem204280 (_4144 : nat) (h1 : term10) : term195 _4144.
Proof. exact (EQ_MP (@lem204277 _4144) (@lem204266 _4144 h1)). Qed.
Lemma lem204281 (n : nat) (h1 : term10) : term195 n.
Proof. exact (@lem204280 n h1). Qed.
Lemma lem204284 (n : nat) (h1 : term10) (h2 : term52 n) : (term19 n) = (NUMERAL 0).
Proof. exact (@lem204281 n h1 (@lem204233 n h2)). Qed.
Lemma lem204285 (n : nat) (h1 : term10) (h2 : term52 n) : term196 n.
Proof. exact (fun h0 : term48 n => @lem204284 n h1 h2). Qed.
Lemma lem204287 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem204288 (n : nat) : (term196 n) = ((term19 n) = (NUMERAL 0)).
Proof. exact (@lem204287 ((term19 n) = (NUMERAL 0))). Qed.
Lemma lem204289 (n : nat) (h1 : term10) (h2 : term52 n) : (term19 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem204288 n) (@lem204285 n h1 h2)). Qed.
Lemma lem204292 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem204294 (n : nat) : (term48 n) = (term197 n).
Proof. exact (@lem204292 ((term19 n) = (NUMERAL 0))). Qed.
Lemma lem204297 (n : nat) (h1 : term52 n) : term197 n.
Proof. exact (EQ_MP (@lem204294 n) (@lem204121 n h1)). Qed.
Lemma lem204300 (n : nat) (h1 : term10) (h2 : term52 n) : False.
Proof. exact (@lem204297 n h2 (@lem204289 n h1 h2)). Qed.
Lemma lem204301 (n : nat) (h1 : term10) (h2 : term52 n) : term198.
Proof. exact (fun h0 : ~ False => @lem204300 n h1 h2). Qed.
Lemma lem204303 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem204304 : term198 = False.
Proof. exact (@lem204303 False). Qed.
Lemma lem204305 (n : nat) (h1 : term10) (h2 : term52 n) : False.
Proof. exact (EQ_MP (@lem204304) (@lem204301 n h1 h2)). Qed.
Lemma lem204372 (n : nat) (h1 : term56 n) : term54 n.
Proof. exact (proj1 (@lem203869 n h1)). Qed.
Lemma lem204373 (n : nat) (h1 : term56 n) : term199 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem204372 n h1). Qed.
Lemma lem204375 (p : Prop) : (term200 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem204376 (n : nat) : (term199 n) = (term54 n).
Proof. exact (@lem204375 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem204377 (n : nat) (h1 : term56 n) : term54 n.
Proof. exact (EQ_MP (@lem204376 n) (@lem204373 n h1)). Qed.
Lemma lem204379 (b : Prop) (a : Prop) : (a \/ b) = (term190 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem204382 (_4154 : nat) : (term102 _4154) = (term201 _4154).
Proof. exact (@lem204379 (Coq.Arith.PeanoNat.Nat.Even _4154) (Coq.Arith.PeanoNat.Nat.Odd _4154)). Qed.
Lemma lem204385 (_4154 : nat) (h1 : term26) : term201 _4154.
Proof. exact (EQ_MP (@lem204382 _4154) (@lem204157 _4154 h1)). Qed.
Lemma lem204386 (n : nat) (h1 : term26) : term201 n.
Proof. exact (@lem204385 n h1). Qed.
Lemma lem204389 (n : nat) (h1 : term26) (h2 : term56 n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (@lem204386 n h1 (@lem204377 n h2)). Qed.
Lemma lem204390 (n : nat) (h1 : term26) (h2 : term56 n) : term202 n.
Proof. exact (fun h0 : term24 n => @lem204389 n h1 h2). Qed.
Lemma lem204392 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem204393 (n : nat) : (term202 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (@lem204392 (Coq.Arith.PeanoNat.Nat.Odd n)). Qed.
Lemma lem204394 (n : nat) (h1 : term26) (h2 : term56 n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (EQ_MP (@lem204393 n) (@lem204390 n h1 h2)). Qed.
Lemma lem204400 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem204401 (_4152 : nat) : (term145 _4152) = (term203 _4152).
Proof. exact (@lem204400 ((term19 _4152) = term21) (term24 _4152)). Qed.
Lemma lem204409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem204410 (_4152 : nat) : (term204 _4152) = (term205 _4152).
Proof. exact (MK_COMB (@lem204409) (@lem204401 _4152)). Qed.
Lemma lem204418 (_4152 : nat) : (term203 _4152) = (term203 _4152).
Proof. exact (eq_refl (term203 _4152)). Qed.
Lemma lem204419 (_4152 : nat) : ((term145 _4152) = (term203 _4152)) = ((term203 _4152) = (term203 _4152)).
Proof. exact (MK_COMB (@lem204410 _4152) (@lem204418 _4152)). Qed.
Lemma lem204421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem204422 (x : Prop) : (x = x) = True.
Proof. exact (@lem204421 Prop x). Qed.
Lemma lem204423 (_4152 : nat) : ((term203 _4152) = (term203 _4152)) = True.
Proof. exact (@lem204422 (term203 _4152)). Qed.
Lemma lem204424 (_4152 : nat) : ((term145 _4152) = (term203 _4152)) = True.
Proof. exact (TRANS (@lem204419 _4152) (@lem204423 _4152)). Qed.
Lemma lem204425 (_4152 : nat) : True = ((term145 _4152) = (term203 _4152)).
Proof. exact (SYM (@lem204424 _4152)). Qed.
Lemma lem204426 (_4152 : nat) : (term145 _4152) = (term203 _4152).
Proof. exact (EQ_MP (@lem204425 _4152) (@lem0)). Qed.
Lemma lem204427 (_4152 : nat) (h1 : term23) : term203 _4152.
Proof. exact (EQ_MP (@lem204426 _4152) (@lem204145 _4152 h1)). Qed.
Lemma lem204429 (b : Prop) (a : Prop) : (a \/ b) = (term190 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem204430 (_4152 : nat) : (term203 _4152) = (term206 _4152).
Proof. exact (@lem204429 (term24 _4152) ((term19 _4152) = term21)). Qed.
Lemma lem204432 (a : Prop) : (term192 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem204433 (_4152 : nat) : (term98 _4152) = (Coq.Arith.PeanoNat.Nat.Odd _4152).
Proof. exact (@lem204432 (Coq.Arith.PeanoNat.Nat.Odd _4152)). Qed.
Lemma lem204434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem204435 (_4152 : nat) : (term207 _4152) = (term208 _4152).
Proof. exact (MK_COMB (@lem204434) (@lem204433 _4152)). Qed.
Lemma lem204436 (_4152 : nat) : ((term19 _4152) = term21) = ((term19 _4152) = term21).
Proof. exact (eq_refl ((term19 _4152) = term21)). Qed.
Lemma lem204437 (_4152 : nat) : (term206 _4152) = (term209 _4152).
Proof. exact (MK_COMB (@lem204435 _4152) (@lem204436 _4152)). Qed.
Lemma lem204438 (_4152 : nat) : (term203 _4152) = (term209 _4152).
Proof. exact (TRANS (@lem204430 _4152) (@lem204437 _4152)). Qed.
Lemma lem204441 (_4152 : nat) (h1 : term23) : term209 _4152.
Proof. exact (EQ_MP (@lem204438 _4152) (@lem204427 _4152 h1)). Qed.
Lemma lem204442 (n : nat) (h1 : term23) : term209 n.
Proof. exact (@lem204441 n h1). Qed.
Lemma lem204445 (n : nat) (h1 : term23) (h2 : term26) (h3 : term56 n) : (term19 n) = term21.
Proof. exact (@lem204442 n h1 (@lem204394 n h2 h3)). Qed.
Lemma lem204446 (n : nat) (h1 : term23) (h2 : term26) (h3 : term56 n) : term210 n.
Proof. exact (fun h0 : term184 n => @lem204445 n h1 h2 h3). Qed.
Lemma lem204448 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem204449 (n : nat) : (term210 n) = ((term19 n) = term21).
Proof. exact (@lem204448 ((term19 n) = term21)). Qed.
Lemma lem204450 (n : nat) (h1 : term23) (h2 : term26) (h3 : term56 n) : (term19 n) = term21.
Proof. exact (EQ_MP (@lem204449 n) (@lem204446 n h1 h2 h3)). Qed.
Lemma lem204453 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem204455 (n : nat) : (term184 n) = (term211 n).
Proof. exact (@lem204453 ((term19 n) = term21)). Qed.
Lemma lem204458 (n : nat) (h1 : term56 n) : term211 n.
Proof. exact (EQ_MP (@lem204455 n) (@lem204161 n h1)). Qed.
Lemma lem204461 (n : nat) (h1 : term23) (h2 : term26) (h3 : term56 n) : False.
Proof. exact (@lem204458 n h3 (@lem204450 n h1 h2 h3)). Qed.
Lemma lem204462 (n : nat) (h1 : term23) (h2 : term26) (h3 : term56 n) : term198.
Proof. exact (fun h0 : ~ False => @lem204461 n h1 h2 h3). Qed.
Lemma lem204464 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem204465 : term198 = False.
Proof. exact (@lem204464 False). Qed.
Lemma lem204466 (n : nat) (h1 : term23) (h2 : term26) (h3 : term56 n) : False.
Proof. exact (EQ_MP (@lem204465) (@lem204462 n h1 h2 h3)). Qed.
Lemma lem204467 (n : nat) (h1 : term10) (h2 : term23) (h3 : term26) (h4 : term60 n) : False.
Proof. exact (or_elim (@lem203861 n h4) (fun h0 : term52 n => @lem204305 n h1 h0) (fun h0 : term56 n => @lem204466 n h2 h3 h0)). Qed.
Lemma lem204468 (n : nat) (h1 : term10) (h2 : term23) (h3 : term26) (h4 : term60 n) : (term60 n) = False.
Proof. exact (prop_ext (fun h5 : term60 n => @lem204467 n h1 h2 h3 h4) (fun h5 : False => @lem203861 n h4)). Qed.
Lemma lem204469 (n : nat) (h1 : term10) (h2 : term23) (h3 : term26) (h4 : term60 n) : False.
Proof. exact (EQ_MP (@lem204468 n h1 h2 h3 h4) (@lem203861 n h4)). Qed.
Lemma lem204470 (h1 : term10) (h2 : term23) (h3 : term26) (h4 : term44) : False.
Proof. exact (ex_elim (@lem203285 h4) (fun n : nat => fun h0 : term70 n => @lem204469 n h1 h2 h3 h0)). Qed.
Lemma lem204471 (h1 : term23) (h2 : term26) (h3 : term44) : term8.
Proof. exact (fun h0 : term10 => @lem204470 h0 h1 h2 h3). Qed.
Lemma lem204472 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem204473 (h1 : term23) (h2 : term26) (h3 : term44) : term9.
Proof. exact (EQ_MP (@lem204472) (@lem204471 h1 h2 h3)). Qed.
Lemma lem204474 (h1 : term26) (h2 : term44) : term13.
Proof. exact (fun h0 : term23 => @lem204473 h0 h1 h2). Qed.
Lemma lem204475 (h1 : term44) : term16.
Proof. exact (fun h0 : term26 => @lem204474 h0 h1). Qed.
Lemma lem204476 : term46.
Proof. exact (fun h0 : term44 => @lem204475 h0). Qed.
Lemma lem204477 : term4.
Proof. exact (EQ_MP (@lem203117) (@lem204476)). Qed.
Lemma lem204479 : term4.
Proof. exact (@lem202919 (@lem204477)). Qed.
Lemma lem204480 (h1 : term3) : term15.
Proof. exact (@lem204479 (@lem202904 h1)). Qed.
Lemma lem204481 (h1 : term3) : term12.
Proof. exact (@lem204480 h1 (@lem124808)). Qed.
Lemma lem204482 (h1 : term3) : term8.
Proof. exact (@lem204481 h1 (@lem202889)). Qed.
Lemma lem204483 (h1 : term3) : False.
Proof. exact (@lem204482 h1 (@lem201634)). Qed.
Lemma lem204484 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem204483 h1) (fun h2 : False => @lem202904 h1)). Qed.
Lemma lem204485 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem204484 h1) (@lem202904 h1)). Qed.
Lemma lem204486 : term2.
Proof. exact (fun h0 : term3 => @lem204485 h0). Qed.
Lemma lem204487 : term1.
Proof. exact (EQ_MP (@lem202903) (@lem204486)). Qed.
