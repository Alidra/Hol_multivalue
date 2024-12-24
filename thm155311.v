Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm155311_term_abbrevs.
Require Import DIVMOD_EXIST_0_spec.
Require Import SKOLEM_THM_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem155065 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem155066 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem155073 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem155066 A B P) (@lem155065 A B P)). Qed.
Lemma lem155074 (P : type1605) : (term3 P) = (term4 P).
Proof. exact (@lem155073 nat nat P). Qed.
Lemma lem155075 (m : nat) : (term5 m) = (term6 m).
Proof. exact (@lem155074 (term7 m)). Qed.
Lemma lem155076 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem155077 (q : nat) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem155078 (m : nat) (n : nat) (q : nat) : (term10 m n q) = (term11 m n q).
Proof. exact (MK_COMB (@lem155076 m n) (@lem155077 q)). Qed.
Lemma lem155079 (m : nat) (q : nat) (n : nat) : (term11 m n q) = (term12 m q n).
Proof. exact (eq_refl (term11 m n q)). Qed.
Lemma lem155080 (m : nat) (q : nat) (n : nat) : (term10 m n q) = (term12 m q n).
Proof. exact (TRANS (@lem155078 m n q) (@lem155079 m q n)). Qed.
Lemma lem155081 (m : nat) (n : nat) : (term13 m n) = (term9 m n).
Proof. exact (fun_ext (fun q : nat => @lem155080 m q n)). Qed.
Lemma lem155082 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem155083 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem155082) (@lem155081 m n)). Qed.
Lemma lem155084 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem155083 m n)). Qed.
Lemma lem155085 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155086 (m : nat) : (term5 m) = (term18 m).
Proof. exact (MK_COMB (@lem155085) (@lem155084 m)). Qed.
Lemma lem155087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem155088 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem155087) (@lem155086 m)). Qed.
Lemma lem155089 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem155090 (q : nat -> nat) (n : nat) : (q n) = (q n).
Proof. exact (eq_refl (q n)). Qed.
Lemma lem155091 (m : nat) (q : nat -> nat) (n : nat) : (term21 m q n) = (term22 m q n).
Proof. exact (MK_COMB (@lem155089 m n) (@lem155090 q n)). Qed.
Lemma lem155092 (m : nat) (q : nat -> nat) (n : nat) : (term22 m q n) = (term23 m q n).
Proof. exact (eq_refl (term22 m q n)). Qed.
Lemma lem155093 (m : nat) (q : nat -> nat) (n : nat) : (term21 m q n) = (term23 m q n).
Proof. exact (TRANS (@lem155091 m q n) (@lem155092 m q n)). Qed.
Lemma lem155094 (m : nat) (q : nat -> nat) : (term24 m q) = (term25 m q).
Proof. exact (fun_ext (fun n : nat => @lem155093 m q n)). Qed.
Lemma lem155095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155096 (m : nat) (q : nat -> nat) : (term26 m q) = (term27 m q).
Proof. exact (MK_COMB (@lem155095) (@lem155094 m q)). Qed.
Lemma lem155097 (m : nat) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun q : nat -> nat => @lem155096 m q)). Qed.
Lemma lem155098 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem155099 (m : nat) : (term6 m) = (term30 m).
Proof. exact (MK_COMB (@lem155098) (@lem155097 m)). Qed.
Lemma lem155100 (m : nat) : ((term5 m) = (term6 m)) = ((term18 m) = (term30 m)).
Proof. exact (MK_COMB (@lem155088 m) (@lem155099 m)). Qed.
Lemma lem155101 (m : nat) : (term18 m) = (term30 m).
Proof. exact (EQ_MP (@lem155100 m) (@lem155075 m)). Qed.
Lemma lem155107 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem155066 A B P) (@lem155065 A B P)). Qed.
Lemma lem155108 (P : type1605) : (term3 P) = (term4 P).
Proof. exact (@lem155107 nat nat P). Qed.
Lemma lem155109 (m : nat) (q : nat -> nat) : (term31 m q) = (term32 m q).
Proof. exact (@lem155108 (term33 m q)). Qed.
Lemma lem155110 (m : nat) (q : nat -> nat) (n : nat) : (term34 m q n) = (term35 m q n).
Proof. exact (eq_refl (term34 m q n)). Qed.
Lemma lem155111 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem155112 (m : nat) (q : nat -> nat) (n : nat) (r : nat) : (term36 m q n r) = (term37 m q n r).
Proof. exact (MK_COMB (@lem155110 m q n) (@lem155111 r)). Qed.
Lemma lem155113 (m : nat) (q : nat -> nat) (r : nat) (n : nat) : (term37 m q n r) = (term38 m q r n).
Proof. exact (eq_refl (term37 m q n r)). Qed.
Lemma lem155114 (m : nat) (q : nat -> nat) (r : nat) (n : nat) : (term36 m q n r) = (term38 m q r n).
Proof. exact (TRANS (@lem155112 m q n r) (@lem155113 m q r n)). Qed.
Lemma lem155115 (m : nat) (q : nat -> nat) (n : nat) : (term39 m q n) = (term35 m q n).
Proof. exact (fun_ext (fun r : nat => @lem155114 m q r n)). Qed.
Lemma lem155116 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem155117 (m : nat) (q : nat -> nat) (n : nat) : (term40 m q n) = (term23 m q n).
Proof. exact (MK_COMB (@lem155116) (@lem155115 m q n)). Qed.
Lemma lem155118 (m : nat) (q : nat -> nat) : (term41 m q) = (term25 m q).
Proof. exact (fun_ext (fun n : nat => @lem155117 m q n)). Qed.
Lemma lem155119 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155120 (m : nat) (q : nat -> nat) : (term31 m q) = (term27 m q).
Proof. exact (MK_COMB (@lem155119) (@lem155118 m q)). Qed.
Lemma lem155121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem155122 (m : nat) (q : nat -> nat) : (term42 m q) = (term43 m q).
Proof. exact (MK_COMB (@lem155121) (@lem155120 m q)). Qed.
Lemma lem155123 (m : nat) (q : nat -> nat) (n : nat) : (term34 m q n) = (term35 m q n).
Proof. exact (eq_refl (term34 m q n)). Qed.
Lemma lem155124 (r : nat -> nat) (n : nat) : (r n) = (r n).
Proof. exact (eq_refl (r n)). Qed.
Lemma lem155125 (m : nat) (q : nat -> nat) (r : nat -> nat) (n : nat) : (term44 m q r n) = (term45 m q r n).
Proof. exact (MK_COMB (@lem155123 m q n) (@lem155124 r n)). Qed.
Lemma lem155126 (m : nat) (q : nat -> nat) (r : nat -> nat) (n : nat) : (term45 m q r n) = (term46 m q r n).
Proof. exact (eq_refl (term45 m q r n)). Qed.
Lemma lem155127 (m : nat) (q : nat -> nat) (r : nat -> nat) (n : nat) : (term44 m q r n) = (term46 m q r n).
Proof. exact (TRANS (@lem155125 m q r n) (@lem155126 m q r n)). Qed.
Lemma lem155128 (m : nat) (q : nat -> nat) (r : nat -> nat) : (term47 m q r) = (term48 m q r).
Proof. exact (fun_ext (fun n : nat => @lem155127 m q r n)). Qed.
Lemma lem155129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155130 (m : nat) (q : nat -> nat) (r : nat -> nat) : (term49 m q r) = (term50 m q r).
Proof. exact (MK_COMB (@lem155129) (@lem155128 m q r)). Qed.
Lemma lem155131 (m : nat) (q : nat -> nat) : (term51 m q) = (term52 m q).
Proof. exact (fun_ext (fun r : nat -> nat => @lem155130 m q r)). Qed.
Lemma lem155132 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem155133 (m : nat) (q : nat -> nat) : (term32 m q) = (term53 m q).
Proof. exact (MK_COMB (@lem155132) (@lem155131 m q)). Qed.
Lemma lem155134 (m : nat) (q : nat -> nat) : ((term31 m q) = (term32 m q)) = ((term27 m q) = (term53 m q)).
Proof. exact (MK_COMB (@lem155122 m q) (@lem155133 m q)). Qed.
Lemma lem155135 (m : nat) (q : nat -> nat) : (term27 m q) = (term53 m q).
Proof. exact (EQ_MP (@lem155134 m q) (@lem155109 m q)). Qed.
Lemma lem155158 (m : nat) : (term29 m) = (term54 m).
Proof. exact (fun_ext (fun q : nat -> nat => @lem155135 m q)). Qed.
Lemma lem155159 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem155160 (m : nat) : (term30 m) = (term55 m).
Proof. exact (MK_COMB (@lem155159) (@lem155158 m)). Qed.
Lemma lem155165 (m : nat) : (term18 m) = (term55 m).
Proof. exact (TRANS (@lem155101 m) (@lem155160 m)). Qed.
Lemma lem155166 : term56 = term57.
Proof. exact (fun_ext (fun m : nat => @lem155165 m)). Qed.
Lemma lem155167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155168 : term58 = term59.
Proof. exact (MK_COMB (@lem155167) (@lem155166)). Qed.
Lemma lem155170 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem155066 A B P) (@lem155065 A B P)). Qed.
Lemma lem155171 (P : type1586) : (term60 P) = (term61 P).
Proof. exact (@lem155170 nat (nat -> nat) P). Qed.
Lemma lem155172 : term62 = term63.
Proof. exact (@lem155171 term64). Qed.
Lemma lem155173 (m : nat) : (term65 m) = (term54 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem155174 (q : nat -> nat) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem155175 (m : nat) (q : nat -> nat) : (term66 m q) = (term67 m q).
Proof. exact (MK_COMB (@lem155173 m) (@lem155174 q)). Qed.
Lemma lem155176 (m : nat) (q : nat -> nat) : (term67 m q) = (term53 m q).
Proof. exact (eq_refl (term67 m q)). Qed.
Lemma lem155177 (m : nat) (q : nat -> nat) : (term66 m q) = (term53 m q).
Proof. exact (TRANS (@lem155175 m q) (@lem155176 m q)). Qed.
Lemma lem155178 (m : nat) : (term68 m) = (term54 m).
Proof. exact (fun_ext (fun q : nat -> nat => @lem155177 m q)). Qed.
Lemma lem155179 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem155180 (m : nat) : (term69 m) = (term55 m).
Proof. exact (MK_COMB (@lem155179) (@lem155178 m)). Qed.
Lemma lem155181 : term70 = term57.
Proof. exact (fun_ext (fun m : nat => @lem155180 m)). Qed.
Lemma lem155182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155183 : term62 = term59.
Proof. exact (MK_COMB (@lem155182) (@lem155181)). Qed.
Lemma lem155184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem155185 : term71 = term72.
Proof. exact (MK_COMB (@lem155184) (@lem155183)). Qed.
Lemma lem155186 (m : nat) : (term65 m) = (term54 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem155187 (q : type1606) (m : nat) : (q m) = (q m).
Proof. exact (eq_refl (q m)). Qed.
Lemma lem155188 (q : type1606) (m : nat) : (term73 q m) = (term74 q m).
Proof. exact (MK_COMB (@lem155186 m) (@lem155187 q m)). Qed.
Lemma lem155189 (q : type1606) (m : nat) : (term74 q m) = (term75 q m).
Proof. exact (eq_refl (term74 q m)). Qed.
Lemma lem155190 (q : type1606) (m : nat) : (term73 q m) = (term75 q m).
Proof. exact (TRANS (@lem155188 q m) (@lem155189 q m)). Qed.
Lemma lem155191 (q : type1606) : (term76 q) = (term77 q).
Proof. exact (fun_ext (fun m : nat => @lem155190 q m)). Qed.
Lemma lem155192 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155193 (q : type1606) : (term78 q) = (term79 q).
Proof. exact (MK_COMB (@lem155192) (@lem155191 q)). Qed.
Lemma lem155194 : term80 = term81.
Proof. exact (fun_ext (fun q : type1606 => @lem155193 q)). Qed.
Lemma lem155195 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem155196 : term63 = term82.
Proof. exact (MK_COMB (@lem155195) (@lem155194)). Qed.
Lemma lem155197 : (term62 = term63) = (term59 = term82).
Proof. exact (MK_COMB (@lem155185) (@lem155196)). Qed.
Lemma lem155198 : term59 = term82.
Proof. exact (EQ_MP (@lem155197) (@lem155172)). Qed.
Lemma lem155204 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem155066 A B P) (@lem155065 A B P)). Qed.
Lemma lem155205 (P : type1586) : (term60 P) = (term61 P).
Proof. exact (@lem155204 nat (nat -> nat) P). Qed.
Lemma lem155206 (q : type1606) : (term83 q) = (term84 q).
Proof. exact (@lem155205 (term85 q)). Qed.
Lemma lem155207 (q : type1606) (m : nat) : (term86 q m) = (term87 q m).
Proof. exact (eq_refl (term86 q m)). Qed.
Lemma lem155208 (r : nat -> nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem155209 (q : type1606) (m : nat) (r : nat -> nat) : (term88 q m r) = (term89 q m r).
Proof. exact (MK_COMB (@lem155207 q m) (@lem155208 r)). Qed.
Lemma lem155210 (q : type1606) (m : nat) (r : nat -> nat) : (term89 q m r) = (term90 q m r).
Proof. exact (eq_refl (term89 q m r)). Qed.
Lemma lem155211 (q : type1606) (m : nat) (r : nat -> nat) : (term88 q m r) = (term90 q m r).
Proof. exact (TRANS (@lem155209 q m r) (@lem155210 q m r)). Qed.
Lemma lem155212 (q : type1606) (m : nat) : (term91 q m) = (term87 q m).
Proof. exact (fun_ext (fun r : nat -> nat => @lem155211 q m r)). Qed.
Lemma lem155213 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem155214 (q : type1606) (m : nat) : (term92 q m) = (term75 q m).
Proof. exact (MK_COMB (@lem155213) (@lem155212 q m)). Qed.
Lemma lem155215 (q : type1606) : (term93 q) = (term77 q).
Proof. exact (fun_ext (fun m : nat => @lem155214 q m)). Qed.
Lemma lem155216 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155217 (q : type1606) : (term83 q) = (term79 q).
Proof. exact (MK_COMB (@lem155216) (@lem155215 q)). Qed.
Lemma lem155218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem155219 (q : type1606) : (term94 q) = (term95 q).
Proof. exact (MK_COMB (@lem155218) (@lem155217 q)). Qed.
Lemma lem155220 (q : type1606) (m : nat) : (term86 q m) = (term87 q m).
Proof. exact (eq_refl (term86 q m)). Qed.
Lemma lem155221 (r : type1606) (m : nat) : (r m) = (r m).
Proof. exact (eq_refl (r m)). Qed.
Lemma lem155222 (q : type1606) (r : type1606) (m : nat) : (term96 q r m) = (term97 q r m).
Proof. exact (MK_COMB (@lem155220 q m) (@lem155221 r m)). Qed.
Lemma lem155223 (q : type1606) (r : type1606) (m : nat) : (term97 q r m) = (term98 q r m).
Proof. exact (eq_refl (term97 q r m)). Qed.
Lemma lem155224 (q : type1606) (r : type1606) (m : nat) : (term96 q r m) = (term98 q r m).
Proof. exact (TRANS (@lem155222 q r m) (@lem155223 q r m)). Qed.
Lemma lem155225 (q : type1606) (r : type1606) : (term99 q r) = (term100 q r).
Proof. exact (fun_ext (fun m : nat => @lem155224 q r m)). Qed.
Lemma lem155226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem155227 (q : type1606) (r : type1606) : (term101 q r) = (term102 q r).
Proof. exact (MK_COMB (@lem155226) (@lem155225 q r)). Qed.
Lemma lem155228 (q : type1606) : (term103 q) = (term104 q).
Proof. exact (fun_ext (fun r : type1606 => @lem155227 q r)). Qed.
Lemma lem155229 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem155230 (q : type1606) : (term84 q) = (term105 q).
Proof. exact (MK_COMB (@lem155229) (@lem155228 q)). Qed.
Lemma lem155231 (q : type1606) : ((term83 q) = (term84 q)) = ((term79 q) = (term105 q)).
Proof. exact (MK_COMB (@lem155219 q) (@lem155230 q)). Qed.
Lemma lem155232 (q : type1606) : (term79 q) = (term105 q).
Proof. exact (EQ_MP (@lem155231 q) (@lem155206 q)). Qed.
Lemma lem155259 : term81 = term106.
Proof. exact (fun_ext (fun q : type1606 => @lem155232 q)). Qed.
Lemma lem155260 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem155261 : term82 = term107.
Proof. exact (MK_COMB (@lem155260) (@lem155259)). Qed.
Lemma lem155266 : term59 = term107.
Proof. exact (TRANS (@lem155198) (@lem155261)). Qed.
Lemma lem155267 : term58 = term107.
Proof. exact (TRANS (@lem155168) (@lem155266)). Qed.
Lemma lem155268 : term107.
Proof. exact (EQ_MP (@lem155267) (@lem155064)). Qed.
Lemma lem155269 : term108.
Proof. exact (fun _3086 : type1674 => @lem155268). Qed.
Lemma lem155270 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem155271 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem155274 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem155271 A B P) (@lem155270 A B P)). Qed.
Lemma lem155275 (P : type1300) : (term109 P) = (term110 P).
Proof. exact (@lem155274 type1674 type1606 P). Qed.
Lemma lem155276 : term111 = term112.
Proof. exact (@lem155275 term113). Qed.
Lemma lem155277 (_3086 : type1674) : (term114 _3086) = term106.
Proof. exact (eq_refl (term114 _3086)). Qed.
Lemma lem155278 (q : type1606) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem155279 (_3086 : type1674) (q : type1606) : (term115 _3086 q) = (term116 q).
Proof. exact (MK_COMB (@lem155277 _3086) (@lem155278 q)). Qed.
Lemma lem155280 (q : type1606) : (term116 q) = (term105 q).
Proof. exact (eq_refl (term116 q)). Qed.
Lemma lem155281 (_3086 : type1674) (q : type1606) : (term115 _3086 q) = (term105 q).
Proof. exact (TRANS (@lem155279 _3086 q) (@lem155280 q)). Qed.
Lemma lem155282 (_3086 : type1674) : (term117 _3086) = term106.
Proof. exact (fun_ext (fun q : type1606 => @lem155281 _3086 q)). Qed.
Lemma lem155283 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem155284 (_3086 : type1674) : (term118 _3086) = term107.
Proof. exact (MK_COMB (@lem155283) (@lem155282 _3086)). Qed.
Lemma lem155285 : term119 = term120.
Proof. exact (fun_ext (fun _3086 : type1674 => @lem155284 _3086)). Qed.
Lemma lem155286 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem155287 : term111 = term108.
Proof. exact (MK_COMB (@lem155286) (@lem155285)). Qed.
Lemma lem155288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem155289 : term121 = term122.
Proof. exact (MK_COMB (@lem155288) (@lem155287)). Qed.
Lemma lem155290 (_3086 : type1674) : (term114 _3086) = term106.
Proof. exact (eq_refl (term114 _3086)). Qed.
Lemma lem155291 (q : type1306) (_3086 : type1674) : (q _3086) = (q _3086).
Proof. exact (eq_refl (q _3086)). Qed.
Lemma lem155292 (q : type1306) (_3086 : type1674) : (term123 q _3086) = (term124 q _3086).
Proof. exact (MK_COMB (@lem155290 _3086) (@lem155291 q _3086)). Qed.
Lemma lem155293 (q : type1306) (_3086 : type1674) : (term124 q _3086) = (term125 q _3086).
Proof. exact (eq_refl (term124 q _3086)). Qed.
Lemma lem155294 (q : type1306) (_3086 : type1674) : (term123 q _3086) = (term125 q _3086).
Proof. exact (TRANS (@lem155292 q _3086) (@lem155293 q _3086)). Qed.
Lemma lem155295 (q : type1306) : (term126 q) = (term127 q).
Proof. exact (fun_ext (fun _3086 : type1674 => @lem155294 q _3086)). Qed.
Lemma lem155296 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem155297 (q : type1306) : (term128 q) = (term129 q).
Proof. exact (MK_COMB (@lem155296) (@lem155295 q)). Qed.
Lemma lem155298 : term130 = term131.
Proof. exact (fun_ext (fun q : type1306 => @lem155297 q)). Qed.
Lemma lem155299 : (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)) = (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat))). Qed.
Lemma lem155300 : term112 = term132.
Proof. exact (MK_COMB (@lem155299) (@lem155298)). Qed.
Lemma lem155301 : (term111 = term112) = (term108 = term132).
Proof. exact (MK_COMB (@lem155289) (@lem155300)). Qed.
Lemma lem155302 : term108 = term132.
Proof. exact (EQ_MP (@lem155301) (@lem155276)). Qed.
Lemma lem155303 : term132.
Proof. exact (EQ_MP (@lem155302) (@lem155269)). Qed.
Lemma lem155305 {A : Type'} : (@ex A) = (term133 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem155306 : (@ex ((prod nat (prod nat nat)) -> nat -> nat -> nat)) = term134.
Proof. exact (@lem155305 type1306). Qed.
Lemma lem155307 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem155308 : term132 = term135.
Proof. exact (MK_COMB (@lem155306) (@lem155307)). Qed.
Lemma lem155309 : term135 = term136.
Proof. exact (eq_refl term135). Qed.
Lemma lem155310 : term132 = term136.
Proof. exact (TRANS (@lem155308) (@lem155309)). Qed.
Lemma lem155311 : term136.
Proof. exact (EQ_MP (@lem155310) (@lem155303)). Qed.
