Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2541190_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import INT_DIVMOD_UNIQ_spec.
Require Import INT_DIV_0_spec.
Require Import INT_REM_0_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482678_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2538106 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2538107 (m : int) (h1 : term0) : term1 m.
Proof. exact (@lem2538106 h1 m). Qed.
Lemma lem2538108 (m : int) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2538109 (m : int) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem2538108 m) (@lem2538107 m h1)). Qed.
Lemma lem2538110 (m : int) (n : int) (h1 : term0) : term3 m n.
Proof. exact (@lem2538109 m h1 n). Qed.
Lemma lem2538111 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2538112 (m : int) (n : int) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem2538111 m n) (@lem2538110 m n h1)). Qed.
Lemma lem2538113 (m : int) (n : int) (q : int) (h1 : term0) : term5 m n q.
Proof. exact (@lem2538112 m n h1 q). Qed.
Lemma lem2538114 (q : int) (m : int) (n : int) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem2538115 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (EQ_MP (@lem2538114 q m n) (@lem2538113 m n q h1)). Qed.
Lemma lem2538116 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term7 q m n r.
Proof. exact (@lem2538115 q m n h1 r). Qed.
Lemma lem2538117 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2538118 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (EQ_MP (@lem2538117 q m n r) (@lem2538116 q m n r h1)). Qed.
Lemma lem2538119 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem2538120 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2538118 q m n r h1 (@lem2538119 m q r n h2)). Qed.
Lemma lem2538121 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term11 q m n r.
Proof. exact (fun h0 : term0 => @lem2538120 m q r n h0 h1). Qed.
Lemma lem2538122 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2538123 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2538121 m q r n h2 (@lem2538122 h1)). Qed.
Lemma lem2538124 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (fun h0 : term9 m q r n => @lem2538123 m q r n h1 h0). Qed.
Lemma lem2538125 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (fun r : int => @lem2538124 q m n r h1). Qed.
Lemma lem2538126 (q : int) (m : int) (h1 : term0) : term12 q m.
Proof. exact (fun n : int => @lem2538125 q m n h1). Qed.
Lemma lem2538127 (q : int) (h1 : term0) : term13 q.
Proof. exact (fun m : int => @lem2538126 q m h1). Qed.
Lemma lem2538128 (h1 : term0) : term14.
Proof. exact (fun q : int => @lem2538127 q h1). Qed.
Lemma lem2538129 : term15.
Proof. exact (fun h0 : term0 => @lem2538128 h0). Qed.
Lemma lem2538130 : term14.
Proof. exact (@lem2538129 (@lem2495588)). Qed.
Lemma lem2538131 (q : int) : term16 q.
Proof. exact (@lem2538130 q). Qed.
Lemma lem2538132 (q : int) : (term16 q) = (term13 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem2538133 (q : int) : term13 q.
Proof. exact (EQ_MP (@lem2538132 q) (@lem2538131 q)). Qed.
Lemma lem2538134 (q : int) (m : int) : term17 q m.
Proof. exact (@lem2538133 q m). Qed.
Lemma lem2538135 (q : int) (m : int) : (term17 q m) = (term12 q m).
Proof. exact (eq_refl (term17 q m)). Qed.
Lemma lem2538136 (q : int) (m : int) : term12 q m.
Proof. exact (EQ_MP (@lem2538135 q m) (@lem2538134 q m)). Qed.
Lemma lem2538137 (q : int) (m : int) (n : int) : term18 q m n.
Proof. exact (@lem2538136 q m n). Qed.
Lemma lem2538138 (q : int) (m : int) (n : int) : (term18 q m n) = (term6 q m n).
Proof. exact (eq_refl (term18 q m n)). Qed.
Lemma lem2538139 (q : int) (m : int) (n : int) : term6 q m n.
Proof. exact (EQ_MP (@lem2538138 q m n) (@lem2538137 q m n)). Qed.
Lemma lem2538140 (q : int) (m : int) (n : int) (r : int) : term7 q m n r.
Proof. exact (@lem2538139 q m n r). Qed.
Lemma lem2538141 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2538153 {A : Type'} (P : A -> Prop) : term19 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem2538154 {A : Type'} (P : A -> Prop) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem2538155 {A : Type'} (P : A -> Prop) : term20 A P.
Proof. exact (EQ_MP (@lem2538154 A P) (@lem2538153 A P)). Qed.
Lemma lem2538156 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term21 A P Q.
Proof. exact (@lem2538155 A P Q). Qed.
Lemma lem2538157 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term21 A P Q) = ((term22 A P Q) = (term23 A P Q)).
Proof. exact (eq_refl (term21 A P Q)). Qed.
Lemma lem2538160 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term22 A P Q) = (term23 A P Q).
Proof. exact (EQ_MP (@lem2538157 A P Q) (@lem2538156 A P Q)). Qed.
Lemma lem2538161 (P : int -> Prop) (Q : int -> Prop) : (term24 P Q) = (term25 P Q).
Proof. exact (@lem2538160 int P Q). Qed.
Lemma lem2538162 : term26 = term27.
Proof. exact (@lem2538161 term28 term29). Qed.
Lemma lem2538163 (n : int) : (term30 n) = ((div n n) = (term31 n)).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2538164 : term32 = term28.
Proof. exact (fun_ext (fun n : int => @lem2538163 n)). Qed.
Lemma lem2538165 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538166 : term33 = term34.
Proof. exact (MK_COMB (@lem2538165) (@lem2538164)). Qed.
Lemma lem2538167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2538168 : term35 = term36.
Proof. exact (MK_COMB (@lem2538167) (@lem2538166)). Qed.
Lemma lem2538169 (n : int) : (term37 n) = ((rem n n) = term38).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem2538170 : term39 = term29.
Proof. exact (fun_ext (fun n : int => @lem2538169 n)). Qed.
Lemma lem2538171 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538172 : term40 = term41.
Proof. exact (MK_COMB (@lem2538171) (@lem2538170)). Qed.
Lemma lem2538173 : term26 = term42.
Proof. exact (MK_COMB (@lem2538168) (@lem2538172)). Qed.
Lemma lem2538174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2538175 : term43 = term44.
Proof. exact (MK_COMB (@lem2538174) (@lem2538173)). Qed.
Lemma lem2538176 (n : int) : (term30 n) = ((div n n) = (term31 n)).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2538177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2538178 (n : int) : (term45 n) = (term46 n).
Proof. exact (MK_COMB (@lem2538177) (@lem2538176 n)). Qed.
Lemma lem2538179 (n : int) : (term37 n) = ((rem n n) = term38).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem2538180 (n : int) : (term47 n) = (term48 n).
Proof. exact (MK_COMB (@lem2538178 n) (@lem2538179 n)). Qed.
Lemma lem2538181 : term49 = term50.
Proof. exact (fun_ext (fun n : int => @lem2538180 n)). Qed.
Lemma lem2538182 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538183 : term27 = term51.
Proof. exact (MK_COMB (@lem2538182) (@lem2538181)). Qed.
Lemma lem2538184 : (term26 = term27) = (term42 = term51).
Proof. exact (MK_COMB (@lem2538175) (@lem2538183)). Qed.
Lemma lem2538185 : term42 = term51.
Proof. exact (EQ_MP (@lem2538184) (@lem2538162)). Qed.
Lemma lem2538200 : term51 = term42.
Proof. exact (SYM (@lem2538185)). Qed.
Lemma lem2538201 (_474 : int) (_475 : Prop) (_476 : int -> Prop) (_477 : int) : (term52 _476 _475 _474 _477) = (term53 _474 _475 _476 _477).
Proof. exact (@lem13473 int _474 _475 _476 _477). Qed.
Lemma lem2538202 (_474 : int) (_475 : Prop) (n : int) (_477 : int) : (term54 n _475 _474 _477) = (term55 _474 _475 n _477).
Proof. exact (@lem2538201 _474 _475 (term56 n) _477). Qed.
Lemma lem2538203 (n : int) : (term57 n) = (term58 n).
Proof. exact (@lem2538202 term38 (n = term38) n term59). Qed.
Lemma lem2538204 (n : int) : (term60 n) = (term61 n).
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem2538205 (n : int) : (term62 n) = (term62 n).
Proof. exact (eq_refl (term62 n)). Qed.
Lemma lem2538206 (n : int) : (term63 n) = (term64 n).
Proof. exact (MK_COMB (@lem2538205 n) (@lem2538204 n)). Qed.
Lemma lem2538207 (n : int) : (term65 n) = (term66 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem2538208 (n : int) : (term67 n) = (term67 n).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem2538209 (n : int) : (term68 n) = (term69 n).
Proof. exact (MK_COMB (@lem2538208 n) (@lem2538207 n)). Qed.
Lemma lem2538210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2538211 (n : int) : (term70 n) = (term71 n).
Proof. exact (MK_COMB (@lem2538210) (@lem2538209 n)). Qed.
Lemma lem2538212 (n : int) : (term58 n) = (term72 n).
Proof. exact (MK_COMB (@lem2538211 n) (@lem2538206 n)). Qed.
Lemma lem2538213 (n : int) : (term57 n) = (term48 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem2538214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2538215 (n : int) : (term73 n) = (term74 n).
Proof. exact (MK_COMB (@lem2538214) (@lem2538213 n)). Qed.
Lemma lem2538216 (n : int) : ((term57 n) = (term58 n)) = ((term48 n) = (term72 n)).
Proof. exact (MK_COMB (@lem2538215 n) (@lem2538212 n)). Qed.
Lemma lem2538217 (n : int) : (term48 n) = (term72 n).
Proof. exact (EQ_MP (@lem2538216 n) (@lem2538203 n)). Qed.
Lemma lem2538218 (n : int) : (term72 n) = (term48 n).
Proof. exact (SYM (@lem2538217 n)). Qed.
Lemma lem2538219 (n : int) (h1 : n = term38) : n = term38.
Proof. exact (h1). Qed.
Lemma lem2538236 (n : int) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem2538254 (p : Prop) : p = (term76 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2538255 (n : int) : (term66 n) = (term77 n).
Proof. exact (@lem2538254 (term66 n)). Qed.
Lemma lem2538256 (n : int) : (term77 n) = (term66 n).
Proof. exact (SYM (@lem2538255 n)). Qed.
Lemma lem2538257 (n : int) (h1 : term78 n) : term78 n.
Proof. exact (h1). Qed.
Lemma lem2538260 (n : int) (h1 : term79 n) : term79 n.
Proof. exact (h1). Qed.
Lemma lem2538261 (n : int) : term80 n.
Proof. exact (fun h0 : term79 n => @lem2538260 n h0). Qed.
Lemma lem2538262 (n : int) (h1 : term80 n) : term80 n.
Proof. exact (h1). Qed.
Lemma lem2538263 (n : int) (h1 : term79 n) : term79 n.
Proof. exact (h1). Qed.
Lemma lem2538264 (n : int) (h1 : term79 n) (h2 : term80 n) : term79 n.
Proof. exact (@lem2538262 n h2 (@lem2538263 n h1)). Qed.
Lemma lem2538265 (n : int) (h1 : term79 n) : term81 n.
Proof. exact (fun h0 : term80 n => @lem2538264 n h1 h0). Qed.
Lemma lem2538266 (n : int) (h1 : term80 n) : term80 n.
Proof. exact (h1). Qed.
Lemma lem2538267 (n : int) (h1 : term79 n) (h2 : term80 n) : term79 n.
Proof. exact (@lem2538265 n h1 (@lem2538266 n h2)). Qed.
Lemma lem2538268 (n : int) (h1 : term80 n) : term80 n.
Proof. exact (fun h0 : term79 n => @lem2538267 n h0 h1). Qed.
Lemma lem2538269 (n : int) : term82 n.
Proof. exact (fun h0 : term80 n => @lem2538268 n h0). Qed.
Lemma lem2538272 (n : int) : term80 n.
Proof. exact (@lem2538269 n (@lem2538261 n)). Qed.
Lemma lem2538290 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2538291 : term83 = term84.
Proof. exact (@lem2538290 term85). Qed.
Lemma lem2538296 : term86 = term86.
Proof. exact (eq_refl term86). Qed.
Lemma lem2538297 : term87 = term88.
Proof. exact (MK_COMB (@lem2538296) (@lem2538291)). Qed.
Lemma lem2538300 (n : int) : (term89 n) = (term89 n).
Proof. exact (eq_refl (term89 n)). Qed.
Lemma lem2538301 (n : int) : (term90 n) = (term91 n).
Proof. exact (MK_COMB (@lem2538300 n) (@lem2538297)). Qed.
Lemma lem2538304 (n : int) : (term67 n) = (term67 n).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem2538305 (n : int) : (term79 n) = (term92 n).
Proof. exact (MK_COMB (@lem2538304 n) (@lem2538301 n)). Qed.
Lemma lem2538308 : term93 = term94.
Proof. exact (fun_ext (fun n : int => @lem2538305 n)). Qed.
Lemma lem2538309 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538318 : term95 = term96.
Proof. exact (MK_COMB (@lem2538309) (@lem2538308)). Qed.
Lemma lem2538319 (m : int) : ((term97 m) = term38) = ((term97 m) = term38).
Proof. exact (eq_refl ((term97 m) = term38)). Qed.
Lemma lem2538320 : term98 = term98.
Proof. exact (fun_ext (fun m : int => @lem2538319 m)). Qed.
Lemma lem2538321 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538322 : term85 = term85.
Proof. exact (MK_COMB (@lem2538321) (@lem2538320)). Qed.
Lemma lem2538323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2538324 : term84 = term84.
Proof. exact (MK_COMB (@lem2538323) (@lem2538322)). Qed.
Lemma lem2538325 (m : int) : ((term99 m) = m) = ((term99 m) = m).
Proof. exact (eq_refl ((term99 m) = m)). Qed.
Lemma lem2538326 : term100 = term100.
Proof. exact (fun_ext (fun m : int => @lem2538325 m)). Qed.
Lemma lem2538327 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538328 : term101 = term101.
Proof. exact (MK_COMB (@lem2538327) (@lem2538326)). Qed.
Lemma lem2538329 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2538330 : term86 = term86.
Proof. exact (MK_COMB (@lem2538329) (@lem2538328)). Qed.
Lemma lem2538331 : term88 = term88.
Proof. exact (MK_COMB (@lem2538330) (@lem2538324)). Qed.
Lemma lem2538340 (n : int) : (term89 n) = (term89 n).
Proof. exact (eq_refl (term89 n)). Qed.
Lemma lem2538341 (n : int) : (term91 n) = (term91 n).
Proof. exact (MK_COMB (@lem2538340 n) (@lem2538331)). Qed.
Lemma lem2538344 (n : int) : (term67 n) = (term67 n).
Proof. exact (eq_refl (term67 n)). Qed.
Lemma lem2538345 (n : int) : (term92 n) = (term92 n).
Proof. exact (MK_COMB (@lem2538344 n) (@lem2538341 n)). Qed.
Lemma lem2538346 : term94 = term94.
Proof. exact (fun_ext (fun n : int => @lem2538345 n)). Qed.
Lemma lem2538347 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538348 : term96 = term96.
Proof. exact (MK_COMB (@lem2538347) (@lem2538346)). Qed.
Lemma lem2538377 : term95 = term96.
Proof. exact (TRANS (@lem2538318) (@lem2538348)). Qed.
Lemma lem2538378 : term96 = term95.
Proof. exact (SYM (@lem2538377)). Qed.
Lemma lem2538380 (n : int) (h1 : term78 n) : term78 n.
Proof. exact (h1). Qed.
Lemma lem2538381 (h1 : term101) : term101.
Proof. exact (h1). Qed.
Lemma lem2538382 (h1 : term85) : term85.
Proof. exact (h1). Qed.
Lemma lem2538388 (n : int) (h1 : n = term38) : n = term38.
Proof. exact (h1). Qed.
Lemma lem2538399 (n : int) : (term78 n) = (term102 n).
Proof. exact (@lem17045 ((div n n) = term38) ((rem n n) = term38)). Qed.
Lemma lem2538401 (m : int) : ((term99 m) = m) = ((term99 m) = m).
Proof. exact (eq_refl ((term99 m) = m)). Qed.
Lemma lem2538402 : term100 = term100.
Proof. exact (fun_ext (fun m : int => @lem2538401 m)). Qed.
Lemma lem2538403 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538412 : term101 = term101.
Proof. exact (MK_COMB (@lem2538403) (@lem2538402)). Qed.
Lemma lem2538413 (h1 : term101) : term101.
Proof. exact (EQ_MP (@lem2538412) (@lem2538381 h1)). Qed.
Lemma lem2538414 (m : int) : ((term97 m) = term38) = ((term97 m) = term38).
Proof. exact (eq_refl ((term97 m) = term38)). Qed.
Lemma lem2538415 : term98 = term98.
Proof. exact (fun_ext (fun m : int => @lem2538414 m)). Qed.
Lemma lem2538416 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538425 : term85 = term85.
Proof. exact (MK_COMB (@lem2538416) (@lem2538415)). Qed.
Lemma lem2538426 (h1 : term85) : term85.
Proof. exact (EQ_MP (@lem2538425) (@lem2538382 h1)). Qed.
Lemma lem2538436 (n : int) (h1 : n = term38) : n = term38.
Proof. exact (h1). Qed.
Lemma lem2538470 (n : int) (h1 : term78 n) : term102 n.
Proof. exact (EQ_MP (@lem2538399 n) (@lem2538380 n h1)). Qed.
Lemma lem2538483 (m : int) : ((term99 m) = m) = ((term99 m) = m).
Proof. exact (eq_refl ((term99 m) = m)). Qed.
Lemma lem2538484 : term100 = term100.
Proof. exact (fun_ext (fun m : int => @lem2538483 m)). Qed.
Lemma lem2538485 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538486 : term101 = term101.
Proof. exact (MK_COMB (@lem2538485) (@lem2538484)). Qed.
Lemma lem2538487 (h1 : term101) : term101.
Proof. exact (EQ_MP (@lem2538486) (@lem2538413 h1)). Qed.
Lemma lem2538504 (m : int) : ((term97 m) = term38) = ((term97 m) = term38).
Proof. exact (eq_refl ((term97 m) = term38)). Qed.
Lemma lem2538505 : term98 = term98.
Proof. exact (fun_ext (fun m : int => @lem2538504 m)). Qed.
Lemma lem2538506 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538507 : term85 = term85.
Proof. exact (MK_COMB (@lem2538506) (@lem2538505)). Qed.
Lemma lem2538508 (h1 : term85) : term85.
Proof. exact (EQ_MP (@lem2538507) (@lem2538426 h1)). Qed.
Lemma lem2538514 (n : int) (h1 : n = term38) : n = term38.
Proof. exact (h1). Qed.
Lemma lem2538523 (m : int) : ((term97 m) = term38) = ((term97 m) = term38).
Proof. exact (eq_refl ((term97 m) = term38)). Qed.
Lemma lem2538524 : term98 = term98.
Proof. exact (fun_ext (fun m : int => @lem2538523 m)). Qed.
Lemma lem2538525 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538527 : term85 = term85.
Proof. exact (MK_COMB (@lem2538525) (@lem2538524)). Qed.
Lemma lem2538528 (h1 : term85) : term85.
Proof. exact (EQ_MP (@lem2538527) (@lem2538508 h1)). Qed.
Lemma lem2538532 (n : int) (h1 : term103 n) : term103 n.
Proof. exact (h1). Qed.
Lemma lem2538536 (n : int) (h1 : n = term38) : n = term38.
Proof. exact (h1). Qed.
Lemma lem2538538 (m : int) : ((term99 m) = m) = ((term99 m) = m).
Proof. exact (eq_refl ((term99 m) = m)). Qed.
Lemma lem2538539 : term100 = term100.
Proof. exact (fun_ext (fun m : int => @lem2538538 m)). Qed.
Lemma lem2538540 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2538542 : term101 = term101.
Proof. exact (MK_COMB (@lem2538540) (@lem2538539)). Qed.
Lemma lem2538543 (h1 : term101) : term101.
Proof. exact (EQ_MP (@lem2538542) (@lem2538487 h1)). Qed.
Lemma lem2538554 (n : int) (h1 : term104 n) : term104 n.
Proof. exact (h1). Qed.
Lemma lem2538558 (_29872 : int) (h1 : term85) : term105 _29872.
Proof. exact (@lem2538528 h1 _29872). Qed.
Lemma lem2538559 (_29872 : int) : (term105 _29872) = ((term97 _29872) = term38).
Proof. exact (eq_refl (term105 _29872)). Qed.
Lemma lem2538561 (_29873 : int) (h1 : term101) : term106 _29873.
Proof. exact (@lem2538543 h1 _29873). Qed.
Lemma lem2538562 (_29873 : int) : (term106 _29873) = ((term99 _29873) = _29873).
Proof. exact (eq_refl (term106 _29873)). Qed.
Lemma lem2538568 (n : int) (h1 : n = term38) : n = term38.
Proof. exact (h1). Qed.
Lemma lem2538574 (n : int) (h1 : term103 n) : term103 n.
Proof. exact (h1). Qed.
Lemma lem2538576 (n : int) (h1 : n = term38) : n = term38.
Proof. exact (h1). Qed.
Lemma lem2538582 (n : int) (h1 : term104 n) : term104 n.
Proof. exact (h1). Qed.
Lemma lem2538625 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2538626 (n : int) (h1 : n = term38) : (term108 n) = term109.
Proof. exact (MK_COMB (@lem2538625) (@lem2538568 n h1)). Qed.
Lemma lem2538627 : term109 = term110.
Proof. exact (eq_refl term109). Qed.
Lemma lem2538628 (n : int) : (term111 n) = (term111 n).
Proof. exact (eq_refl (term111 n)). Qed.
Lemma lem2538629 (n : int) : ((term108 n) = term109) = ((term108 n) = term110).
Proof. exact (MK_COMB (@lem2538628 n) (@lem2538627)). Qed.
Lemma lem2538630 (n : int) : (term108 n) = (term103 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem2538631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2538632 (n : int) : (term111 n) = (term112 n).
Proof. exact (MK_COMB (@lem2538631) (@lem2538630 n)). Qed.
Lemma lem2538633 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2538634 (n : int) : ((term108 n) = term110) = ((term103 n) = term110).
Proof. exact (MK_COMB (@lem2538632 n) (@lem2538633)). Qed.
Lemma lem2538635 (n : int) : ((term108 n) = term109) = ((term103 n) = term110).
Proof. exact (TRANS (@lem2538629 n) (@lem2538634 n)). Qed.
Lemma lem2538636 (n : int) (h1 : n = term38) : (term103 n) = term110.
Proof. exact (EQ_MP (@lem2538635 n) (@lem2538626 n h1)). Qed.
Lemma lem2538637 (n : int) (h1 : term103 n) (h2 : n = term38) : term110.
Proof. exact (EQ_MP (@lem2538636 n h2) (@lem2538574 n h1)). Qed.
Lemma lem2538680 : term113 = term113.
Proof. exact (eq_refl term113). Qed.
Lemma lem2538681 (n : int) (h1 : n = term38) : (term114 n) = term115.
Proof. exact (MK_COMB (@lem2538680) (@lem2538576 n h1)). Qed.
Lemma lem2538682 : term115 = term116.
Proof. exact (eq_refl term115). Qed.
Lemma lem2538683 (n : int) : (term117 n) = (term117 n).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem2538684 (n : int) : ((term114 n) = term115) = ((term114 n) = term116).
Proof. exact (MK_COMB (@lem2538683 n) (@lem2538682)). Qed.
Lemma lem2538685 (n : int) : (term114 n) = (term104 n).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem2538686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2538687 (n : int) : (term117 n) = (term118 n).
Proof. exact (MK_COMB (@lem2538686) (@lem2538685 n)). Qed.
Lemma lem2538688 : term116 = term116.
Proof. exact (eq_refl term116). Qed.
Lemma lem2538689 (n : int) : ((term114 n) = term116) = ((term104 n) = term116).
Proof. exact (MK_COMB (@lem2538687 n) (@lem2538688)). Qed.
Lemma lem2538690 (n : int) : ((term114 n) = term115) = ((term104 n) = term116).
Proof. exact (TRANS (@lem2538684 n) (@lem2538689 n)). Qed.
Lemma lem2538691 (n : int) (h1 : n = term38) : (term104 n) = term116.
Proof. exact (EQ_MP (@lem2538690 n) (@lem2538681 n h1)). Qed.
Lemma lem2538692 (n : int) (h1 : term104 n) (h2 : n = term38) : term116.
Proof. exact (EQ_MP (@lem2538691 n h2) (@lem2538582 n h1)). Qed.
Lemma lem2538744 (_29872 : int) (h1 : term85) : (term97 _29872) = term38.
Proof. exact (EQ_MP (@lem2538559 _29872) (@lem2538558 _29872 h1)). Qed.
Lemma lem2538745 (h1 : term85) : term119 = term38.
Proof. exact (@lem2538744 term38 h1). Qed.
Lemma lem2538746 (h1 : term85) : term120.
Proof. exact (fun h0 : term110 => @lem2538745 h1). Qed.
Lemma lem2538748 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2538749 : term120 = (term119 = term38).
Proof. exact (@lem2538748 (term119 = term38)). Qed.
Lemma lem2538750 (h1 : term85) : term119 = term38.
Proof. exact (EQ_MP (@lem2538749) (@lem2538746 h1)). Qed.
Lemma lem2538753 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2538755 : term110 = term122.
Proof. exact (@lem2538753 (term119 = term38)). Qed.
Lemma lem2538758 (n : int) (h1 : term103 n) (h2 : n = term38) : term122.
Proof. exact (EQ_MP (@lem2538755) (@lem2538637 n h1 h2)). Qed.
Lemma lem2538761 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (@lem2538758 n h2 h3 (@lem2538750 h1)). Qed.
Lemma lem2538762 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : term123.
Proof. exact (fun h0 : ~ False => @lem2538761 n h1 h2 h3). Qed.
Lemma lem2538764 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2538765 : term123 = False.
Proof. exact (@lem2538764 False). Qed.
Lemma lem2538818 (_29873 : int) (h1 : term101) : (term99 _29873) = _29873.
Proof. exact (EQ_MP (@lem2538562 _29873) (@lem2538561 _29873 h1)). Qed.
Lemma lem2538819 (h1 : term101) : term124 = term38.
Proof. exact (@lem2538818 term38 h1). Qed.
Lemma lem2538820 (h1 : term101) : term125.
Proof. exact (fun h0 : term116 => @lem2538819 h1). Qed.
Lemma lem2538822 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2538823 : term125 = (term124 = term38).
Proof. exact (@lem2538822 (term124 = term38)). Qed.
Lemma lem2538824 (h1 : term101) : term124 = term38.
Proof. exact (EQ_MP (@lem2538823) (@lem2538820 h1)). Qed.
Lemma lem2538827 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2538829 : term116 = term126.
Proof. exact (@lem2538827 (term124 = term38)). Qed.
Lemma lem2538832 (n : int) (h1 : term104 n) (h2 : n = term38) : term126.
Proof. exact (EQ_MP (@lem2538829) (@lem2538692 n h1 h2)). Qed.
Lemma lem2538835 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (@lem2538832 n h2 h3 (@lem2538824 h1)). Qed.
Lemma lem2538836 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : term123.
Proof. exact (fun h0 : ~ False => @lem2538835 n h1 h2 h3). Qed.
Lemma lem2538838 (p : Prop) : (term121 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2538839 : term123 = False.
Proof. exact (@lem2538838 False). Qed.
Lemma lem2538841 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538839) (@lem2538836 n h1 h2 h3)). Qed.
Lemma lem2538842 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538765) (@lem2538762 n h1 h2 h3)). Qed.
Lemma lem2538843 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : (term104 n) = False.
Proof. exact (prop_ext (fun h4 : term104 n => @lem2538841 n h1 h2 h3) (fun h4 : False => @lem2538582 n h2)). Qed.
Lemma lem2538844 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538843 n h1 h2 h3) (@lem2538582 n h2)). Qed.
Lemma lem2538845 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h4 : n = term38 => @lem2538844 n h1 h2 h3) (fun h4 : False => @lem2538576 n h3)). Qed.
Lemma lem2538846 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538845 n h1 h2 h3) (@lem2538576 n h3)). Qed.
Lemma lem2538847 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : (term103 n) = False.
Proof. exact (prop_ext (fun h4 : term103 n => @lem2538842 n h1 h2 h3) (fun h4 : False => @lem2538574 n h2)). Qed.
Lemma lem2538848 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538847 n h1 h2 h3) (@lem2538574 n h2)). Qed.
Lemma lem2538849 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h4 : n = term38 => @lem2538848 n h1 h2 h3) (fun h4 : False => @lem2538568 n h3)). Qed.
Lemma lem2538850 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538849 n h1 h2 h3) (@lem2538568 n h3)). Qed.
Lemma lem2538851 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : (term104 n) = False.
Proof. exact (prop_ext (fun h4 : term104 n => @lem2538846 n h1 h2 h3) (fun h4 : False => @lem2538554 n h2)). Qed.
Lemma lem2538852 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538851 n h1 h2 h3) (@lem2538554 n h2)). Qed.
Lemma lem2538853 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h4 : n = term38 => @lem2538852 n h1 h2 h3) (fun h4 : False => @lem2538536 n h3)). Qed.
Lemma lem2538854 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538853 n h1 h2 h3) (@lem2538536 n h3)). Qed.
Lemma lem2538855 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : (term103 n) = False.
Proof. exact (prop_ext (fun h4 : term103 n => @lem2538850 n h1 h2 h3) (fun h4 : False => @lem2538532 n h2)). Qed.
Lemma lem2538856 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538855 n h1 h2 h3) (@lem2538532 n h2)). Qed.
Lemma lem2538857 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h4 : n = term38 => @lem2538856 n h1 h2 h3) (fun h4 : False => @lem2538514 n h3)). Qed.
Lemma lem2538858 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538857 n h1 h2 h3) (@lem2538514 n h3)). Qed.
Lemma lem2538859 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : (term104 n) = False.
Proof. exact (prop_ext (fun h4 : term104 n => @lem2538854 n h1 h2 h3) (fun h4 : False => @lem2538554 n h2)). Qed.
Lemma lem2538860 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538859 n h1 h2 h3) (@lem2538554 n h2)). Qed.
Lemma lem2538861 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : term101 = False.
Proof. exact (prop_ext (fun h4 : term101 => @lem2538860 n h1 h2 h3) (fun h4 : False => @lem2538543 h1)). Qed.
Lemma lem2538862 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538861 n h1 h2 h3) (@lem2538543 h1)). Qed.
Lemma lem2538863 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h4 : n = term38 => @lem2538862 n h1 h2 h3) (fun h4 : False => @lem2538536 n h3)). Qed.
Lemma lem2538864 (n : int) (h1 : term101) (h2 : term104 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538863 n h1 h2 h3) (@lem2538536 n h3)). Qed.
Lemma lem2538865 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : (term103 n) = False.
Proof. exact (prop_ext (fun h4 : term103 n => @lem2538858 n h1 h2 h3) (fun h4 : False => @lem2538532 n h2)). Qed.
Lemma lem2538866 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538865 n h1 h2 h3) (@lem2538532 n h2)). Qed.
Lemma lem2538867 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : term85 = False.
Proof. exact (prop_ext (fun h4 : term85 => @lem2538866 n h1 h2 h3) (fun h4 : False => @lem2538528 h1)). Qed.
Lemma lem2538868 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538867 n h1 h2 h3) (@lem2538528 h1)). Qed.
Lemma lem2538869 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h4 : n = term38 => @lem2538868 n h1 h2 h3) (fun h4 : False => @lem2538514 n h3)). Qed.
Lemma lem2538870 (n : int) (h1 : term85) (h2 : term103 n) (h3 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538869 n h1 h2 h3) (@lem2538514 n h3)). Qed.
Lemma lem2538871 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : False.
Proof. exact (or_elim (@lem2538470 n h3) (fun h0 : term103 n => @lem2538870 n h1 h0 h4) (fun h0 : term104 n => @lem2538864 n h2 h0 h4)). Qed.
Lemma lem2538872 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : term85 = False.
Proof. exact (prop_ext (fun h5 : term85 => @lem2538871 n h1 h2 h3 h4) (fun h5 : False => @lem2538508 h1)). Qed.
Lemma lem2538873 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538872 n h1 h2 h3 h4) (@lem2538508 h1)). Qed.
Lemma lem2538874 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : term101 = False.
Proof. exact (prop_ext (fun h5 : term101 => @lem2538873 n h1 h2 h3 h4) (fun h5 : False => @lem2538487 h2)). Qed.
Lemma lem2538875 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538874 n h1 h2 h3 h4) (@lem2538487 h2)). Qed.
Lemma lem2538876 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h5 : n = term38 => @lem2538875 n h1 h2 h3 h4) (fun h5 : False => @lem2538436 n h4)). Qed.
Lemma lem2538877 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538876 n h1 h2 h3 h4) (@lem2538436 n h4)). Qed.
Lemma lem2538878 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : term85 = False.
Proof. exact (prop_ext (fun h5 : term85 => @lem2538877 n h1 h2 h3 h4) (fun h5 : False => @lem2538426 h1)). Qed.
Lemma lem2538879 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538878 n h1 h2 h3 h4) (@lem2538426 h1)). Qed.
Lemma lem2538880 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : term101 = False.
Proof. exact (prop_ext (fun h5 : term101 => @lem2538879 n h1 h2 h3 h4) (fun h5 : False => @lem2538413 h2)). Qed.
Lemma lem2538881 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538880 n h1 h2 h3 h4) (@lem2538413 h2)). Qed.
Lemma lem2538882 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : (n = term38) = False.
Proof. exact (prop_ext (fun h5 : n = term38 => @lem2538881 n h1 h2 h3 h4) (fun h5 : False => @lem2538388 n h4)). Qed.
Lemma lem2538883 (n : int) (h1 : term85) (h2 : term101) (h3 : term78 n) (h4 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538882 n h1 h2 h3 h4) (@lem2538388 n h4)). Qed.
Lemma lem2538884 (n : int) (h1 : term101) (h2 : term78 n) (h3 : n = term38) : term83.
Proof. exact (fun h0 : term85 => @lem2538883 n h0 h1 h2 h3). Qed.
Lemma lem2538885 : term83 = term84.
Proof. exact (@lem69 term85). Qed.
Lemma lem2538886 (n : int) (h1 : term101) (h2 : term78 n) (h3 : n = term38) : term84.
Proof. exact (EQ_MP (@lem2538885) (@lem2538884 n h1 h2 h3)). Qed.
Lemma lem2538887 (n : int) (h1 : term78 n) (h2 : n = term38) : term88.
Proof. exact (fun h0 : term101 => @lem2538886 n h0 h1 h2). Qed.
Lemma lem2538888 (n : int) (h1 : n = term38) : term91 n.
Proof. exact (fun h0 : term78 n => @lem2538887 n h0 h1). Qed.
Lemma lem2538889 (n : int) : term92 n.
Proof. exact (fun h0 : n = term38 => @lem2538888 n h0). Qed.
Lemma lem2538894 : term96.
Proof. exact (fun n : int => @lem2538889 n). Qed.
Lemma lem2538895 : term95.
Proof. exact (EQ_MP (@lem2538378) (@lem2538894)). Qed.
Lemma lem2538896 (n : int) : term127 n.
Proof. exact (@lem2538895 n). Qed.
Lemma lem2538897 (n : int) : (term127 n) = (term79 n).
Proof. exact (eq_refl (term127 n)). Qed.
Lemma lem2538898 (n : int) : term79 n.
Proof. exact (EQ_MP (@lem2538897 n) (@lem2538896 n)). Qed.
Lemma lem2538900 (n : int) : term79 n.
Proof. exact (@lem2538272 n (@lem2538898 n)). Qed.
Lemma lem2538901 (n : int) (h1 : n = term38) : term90 n.
Proof. exact (@lem2538900 n (@lem2538219 n h1)). Qed.
Lemma lem2538902 (n : int) (h1 : term78 n) (h2 : n = term38) : term87.
Proof. exact (@lem2538901 n h2 (@lem2538257 n h1)). Qed.
Lemma lem2538903 (n : int) (h1 : term78 n) (h2 : n = term38) : term83.
Proof. exact (@lem2538902 n h1 h2 (@lem2396893)). Qed.
Lemma lem2538904 (n : int) (h1 : term78 n) (h2 : n = term38) : False.
Proof. exact (@lem2538903 n h1 h2 (@lem2395867)). Qed.
Lemma lem2538905 (n : int) (h1 : term78 n) (h2 : n = term38) : (term78 n) = False.
Proof. exact (prop_ext (fun h3 : term78 n => @lem2538904 n h1 h2) (fun h3 : False => @lem2538257 n h1)). Qed.
Lemma lem2538906 (n : int) (h1 : term78 n) (h2 : n = term38) : False.
Proof. exact (EQ_MP (@lem2538905 n h1 h2) (@lem2538257 n h1)). Qed.
Lemma lem2538907 (n : int) (h1 : n = term38) : term77 n.
Proof. exact (fun h0 : term78 n => @lem2538906 n h0 h1). Qed.
Lemma lem2538910 (q : int) (m : int) (n : int) (r : int) : term8 q m n r.
Proof. exact (EQ_MP (@lem2538141 q m n r) (@lem2538140 q m n r)). Qed.
Lemma lem2538911 (n : int) : term128 n.
Proof. exact (@lem2538910 term59 n n term38). Qed.
Lemma lem2538912 (n : int) : (term129 n) = (term130 n).
Proof. exact (@lem2318604 (term130 n)). Qed.
Lemma lem2538932 (n : int) : (term131 n) = (term132 n).
Proof. exact (@lem17045 term133 (term134 n)). Qed.
Lemma lem2538934 (n : int) : (term135 n) = (term135 n).
Proof. exact (eq_refl (term135 n)). Qed.
Lemma lem2538935 (n : int) : (term136 n) = (term137 n).
Proof. exact (MK_COMB (@lem2538934 n) (@lem2538932 n)). Qed.
Lemma lem2538936 (n : int) : (term138 n) = (term136 n).
Proof. exact (@lem17045 (n = (term139 n)) (term140 n)). Qed.
Lemma lem2538937 (n : int) : (term138 n) = (term137 n).
Proof. exact (TRANS (@lem2538936 n) (@lem2538935 n)). Qed.
Lemma lem2538939 (n : int) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem2538940 (n : int) : (term142 n) = (term143 n).
Proof. exact (MK_COMB (@lem2538939 n) (@lem2538937 n)). Qed.
Lemma lem2538941 (n : int) : (term144 n) = (term142 n).
Proof. exact (@lem17362 (term75 n) (term145 n)). Qed.
Lemma lem2538965 (n : int) : (term144 n) = (term143 n).
Proof. exact (TRANS (@lem2538941 n) (@lem2538940 n)). Qed.
Lemma lem2538967 (y : int) (x : int) : (term146 x y) = (term147 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2538968 (n : int) : (term75 n) = (term148 n).
Proof. exact (@lem2538967 term38 n). Qed.
Lemma lem2538970 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2538971 (n : int) : (term150 n) = (term151 n).
Proof. exact (@lem2538970 (term152 n) term38). Qed.
Lemma lem2538973 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2538974 (n : int) : (term155 n) = (term156 n).
Proof. exact (@lem2538973 n term59). Qed.
Lemma lem2538976 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2538977 : term158 = term159.
Proof. exact (@lem2538976 term160). Qed.
Lemma lem2538978 (n : int) : (term161 n) = (term161 n).
Proof. exact (eq_refl (term161 n)). Qed.
Lemma lem2538979 (n : int) : (term156 n) = (term162 n).
Proof. exact (MK_COMB (@lem2538978 n) (@lem2538977)). Qed.
Lemma lem2538980 (n : int) : (term155 n) = (term162 n).
Proof. exact (TRANS (@lem2538974 n) (@lem2538979 n)). Qed.
Lemma lem2538981 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2538982 (n : int) : (term163 n) = (term164 n).
Proof. exact (MK_COMB (@lem2538981) (@lem2538980 n)). Qed.
Lemma lem2538984 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2538985 : term165 = term166.
Proof. exact (@lem2538984 (NUMERAL 0)). Qed.
Lemma lem2538986 (n : int) : (term151 n) = (term167 n).
Proof. exact (MK_COMB (@lem2538982 n) (@lem2538985)). Qed.
Lemma lem2538987 (n : int) : (term150 n) = (term167 n).
Proof. exact (TRANS (@lem2538971 n) (@lem2538986 n)). Qed.
Lemma lem2538988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2538989 (n : int) : (term168 n) = (term169 n).
Proof. exact (MK_COMB (@lem2538988) (@lem2538987 n)). Qed.
Lemma lem2538991 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2538992 (n : int) : (term170 n) = (term171 n).
Proof. exact (@lem2538991 term172 n). Qed.
Lemma lem2538994 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2538995 : term173 = term174.
Proof. exact (@lem2538994 term38 term59). Qed.
Lemma lem2538997 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2538998 : term165 = term166.
Proof. exact (@lem2538997 (NUMERAL 0)). Qed.
Lemma lem2538999 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539000 : term175 = term176.
Proof. exact (MK_COMB (@lem2538999) (@lem2538998)). Qed.
Lemma lem2539002 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539003 : term158 = term159.
Proof. exact (@lem2539002 term160). Qed.
Lemma lem2539004 : term174 = term177.
Proof. exact (MK_COMB (@lem2539000) (@lem2539003)). Qed.
Lemma lem2539005 : term173 = term177.
Proof. exact (TRANS (@lem2538995) (@lem2539004)). Qed.
Lemma lem2539006 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2539007 : term178 = term179.
Proof. exact (MK_COMB (@lem2539006) (@lem2539005)). Qed.
Lemma lem2539008 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2539009 (n : int) : (term171 n) = (term180 n).
Proof. exact (MK_COMB (@lem2539007) (@lem2539008 n)). Qed.
Lemma lem2539010 (n : int) : (term170 n) = (term180 n).
Proof. exact (TRANS (@lem2538992 n) (@lem2539009 n)). Qed.
Lemma lem2539011 (n : int) : (term148 n) = (term181 n).
Proof. exact (MK_COMB (@lem2538989 n) (@lem2539010 n)). Qed.
Lemma lem2539012 (n : int) : (term75 n) = (term181 n).
Proof. exact (TRANS (@lem2538968 n) (@lem2539011 n)). Qed.
Lemma lem2539014 (y : int) (x : int) : (term146 x y) = (term147 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2539015 (n : int) : (term182 n) = (term183 n).
Proof. exact (@lem2539014 (term139 n) n). Qed.
Lemma lem2539017 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2539018 (n : int) : (term184 n) = (term185 n).
Proof. exact (@lem2539017 (term152 n) (term139 n)). Qed.
Lemma lem2539020 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2539021 (n : int) : (term155 n) = (term156 n).
Proof. exact (@lem2539020 n term59). Qed.
Lemma lem2539023 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539024 : term158 = term159.
Proof. exact (@lem2539023 term160). Qed.
Lemma lem2539025 (n : int) : (term161 n) = (term161 n).
Proof. exact (eq_refl (term161 n)). Qed.
Lemma lem2539026 (n : int) : (term156 n) = (term162 n).
Proof. exact (MK_COMB (@lem2539025 n) (@lem2539024)). Qed.
Lemma lem2539027 (n : int) : (term155 n) = (term162 n).
Proof. exact (TRANS (@lem2539021 n) (@lem2539026 n)). Qed.
Lemma lem2539028 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2539029 (n : int) : (term163 n) = (term164 n).
Proof. exact (MK_COMB (@lem2539028) (@lem2539027 n)). Qed.
Lemma lem2539031 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2539032 (n : int) : (term186 n) = (term187 n).
Proof. exact (@lem2539031 (term188 n) term38). Qed.
Lemma lem2539034 (x : int) (y : int) : (term189 x y) = (term190 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2539035 (n : int) : (term191 n) = (term192 n).
Proof. exact (@lem2539034 term59 n). Qed.
Lemma lem2539037 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539038 : term158 = term159.
Proof. exact (@lem2539037 term160). Qed.
Lemma lem2539039 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539040 : term193 = term194.
Proof. exact (MK_COMB (@lem2539039) (@lem2539038)). Qed.
Lemma lem2539041 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2539042 (n : int) : (term192 n) = (term195 n).
Proof. exact (MK_COMB (@lem2539040) (@lem2539041 n)). Qed.
Lemma lem2539043 (n : int) : (term191 n) = (term195 n).
Proof. exact (TRANS (@lem2539035 n) (@lem2539042 n)). Qed.
Lemma lem2539044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539045 (n : int) : (term196 n) = (term197 n).
Proof. exact (MK_COMB (@lem2539044) (@lem2539043 n)). Qed.
Lemma lem2539047 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539048 : term165 = term166.
Proof. exact (@lem2539047 (NUMERAL 0)). Qed.
Lemma lem2539049 (n : int) : (term187 n) = (term198 n).
Proof. exact (MK_COMB (@lem2539045 n) (@lem2539048)). Qed.
Lemma lem2539050 (n : int) : (term186 n) = (term198 n).
Proof. exact (TRANS (@lem2539032 n) (@lem2539049 n)). Qed.
Lemma lem2539051 (n : int) : (term185 n) = (term199 n).
Proof. exact (MK_COMB (@lem2539029 n) (@lem2539050 n)). Qed.
Lemma lem2539052 (n : int) : (term184 n) = (term199 n).
Proof. exact (TRANS (@lem2539018 n) (@lem2539051 n)). Qed.
Lemma lem2539053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539054 (n : int) : (term200 n) = (term201 n).
Proof. exact (MK_COMB (@lem2539053) (@lem2539052 n)). Qed.
Lemma lem2539056 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2539057 (n : int) : (term202 n) = (term203 n).
Proof. exact (@lem2539056 (term204 n) n). Qed.
Lemma lem2539059 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2539060 (n : int) : (term205 n) = (term206 n).
Proof. exact (@lem2539059 (term139 n) term59). Qed.
Lemma lem2539062 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2539063 (n : int) : (term186 n) = (term187 n).
Proof. exact (@lem2539062 (term188 n) term38). Qed.
Lemma lem2539065 (x : int) (y : int) : (term189 x y) = (term190 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2539066 (n : int) : (term191 n) = (term192 n).
Proof. exact (@lem2539065 term59 n). Qed.
Lemma lem2539068 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539069 : term158 = term159.
Proof. exact (@lem2539068 term160). Qed.
Lemma lem2539070 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539071 : term193 = term194.
Proof. exact (MK_COMB (@lem2539070) (@lem2539069)). Qed.
Lemma lem2539072 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2539073 (n : int) : (term192 n) = (term195 n).
Proof. exact (MK_COMB (@lem2539071) (@lem2539072 n)). Qed.
Lemma lem2539074 (n : int) : (term191 n) = (term195 n).
Proof. exact (TRANS (@lem2539066 n) (@lem2539073 n)). Qed.
Lemma lem2539075 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539076 (n : int) : (term196 n) = (term197 n).
Proof. exact (MK_COMB (@lem2539075) (@lem2539074 n)). Qed.
Lemma lem2539078 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539079 : term165 = term166.
Proof. exact (@lem2539078 (NUMERAL 0)). Qed.
Lemma lem2539080 (n : int) : (term187 n) = (term198 n).
Proof. exact (MK_COMB (@lem2539076 n) (@lem2539079)). Qed.
Lemma lem2539081 (n : int) : (term186 n) = (term198 n).
Proof. exact (TRANS (@lem2539063 n) (@lem2539080 n)). Qed.
Lemma lem2539082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539083 (n : int) : (term207 n) = (term208 n).
Proof. exact (MK_COMB (@lem2539082) (@lem2539081 n)). Qed.
Lemma lem2539085 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539086 : term158 = term159.
Proof. exact (@lem2539085 term160). Qed.
Lemma lem2539087 (n : int) : (term206 n) = (term209 n).
Proof. exact (MK_COMB (@lem2539083 n) (@lem2539086)). Qed.
Lemma lem2539088 (n : int) : (term205 n) = (term209 n).
Proof. exact (TRANS (@lem2539060 n) (@lem2539087 n)). Qed.
Lemma lem2539089 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2539090 (n : int) : (term210 n) = (term211 n).
Proof. exact (MK_COMB (@lem2539089) (@lem2539088 n)). Qed.
Lemma lem2539091 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2539092 (n : int) : (term203 n) = (term212 n).
Proof. exact (MK_COMB (@lem2539090 n) (@lem2539091 n)). Qed.
Lemma lem2539093 (n : int) : (term202 n) = (term212 n).
Proof. exact (TRANS (@lem2539057 n) (@lem2539092 n)). Qed.
Lemma lem2539094 (n : int) : (term183 n) = (term213 n).
Proof. exact (MK_COMB (@lem2539054 n) (@lem2539093 n)). Qed.
Lemma lem2539095 (n : int) : (term182 n) = (term213 n).
Proof. exact (TRANS (@lem2539015 n) (@lem2539094 n)). Qed.
Lemma lem2539097 (y : int) (x : int) : (term214 x y) = (term215 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2539098 : term216 = term217.
Proof. exact (@lem2539097 term38 term38). Qed.
Lemma lem2539100 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2539101 : term217 = term218.
Proof. exact (@lem2539100 term172 term38). Qed.
Lemma lem2539103 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2539104 : term173 = term174.
Proof. exact (@lem2539103 term38 term59). Qed.
Lemma lem2539106 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539107 : term165 = term166.
Proof. exact (@lem2539106 (NUMERAL 0)). Qed.
Lemma lem2539108 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539109 : term175 = term176.
Proof. exact (MK_COMB (@lem2539108) (@lem2539107)). Qed.
Lemma lem2539111 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539112 : term158 = term159.
Proof. exact (@lem2539111 term160). Qed.
Lemma lem2539113 : term174 = term177.
Proof. exact (MK_COMB (@lem2539109) (@lem2539112)). Qed.
Lemma lem2539114 : term173 = term177.
Proof. exact (TRANS (@lem2539104) (@lem2539113)). Qed.
Lemma lem2539115 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2539116 : term178 = term179.
Proof. exact (MK_COMB (@lem2539115) (@lem2539114)). Qed.
Lemma lem2539118 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539119 : term165 = term166.
Proof. exact (@lem2539118 (NUMERAL 0)). Qed.
Lemma lem2539120 : term218 = term219.
Proof. exact (MK_COMB (@lem2539116) (@lem2539119)). Qed.
Lemma lem2539121 : term217 = term219.
Proof. exact (TRANS (@lem2539101) (@lem2539120)). Qed.
Lemma lem2539122 : term216 = term219.
Proof. exact (TRANS (@lem2539098) (@lem2539121)). Qed.
Lemma lem2539124 (y : int) (x : int) : (term220 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2539125 (n : int) : (term221 n) = (term222 n).
Proof. exact (@lem2539124 (int_abs n) term38). Qed.
Lemma lem2539127 (x : int) (y : int) : (int_le x y) = (term149 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2539128 (n : int) : (term222 n) = (term223 n).
Proof. exact (@lem2539127 (int_abs n) term38). Qed.
Lemma lem2539130 (x : int) : (term224 x) = (term225 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2539131 (n : int) : (term224 n) = (term225 n).
Proof. exact (@lem2539130 n). Qed.
Lemma lem2539132 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2539133 (n : int) : (term226 n) = (term227 n).
Proof. exact (MK_COMB (@lem2539132) (@lem2539131 n)). Qed.
Lemma lem2539135 (n : nat) : (term157 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2539136 : term165 = term166.
Proof. exact (@lem2539135 (NUMERAL 0)). Qed.
Lemma lem2539137 (n : int) : (term223 n) = (term228 n).
Proof. exact (MK_COMB (@lem2539133 n) (@lem2539136)). Qed.
Lemma lem2539138 (n : int) : (term222 n) = (term228 n).
Proof. exact (TRANS (@lem2539128 n) (@lem2539137 n)). Qed.
Lemma lem2539139 (n : int) : (term221 n) = (term228 n).
Proof. exact (TRANS (@lem2539125 n) (@lem2539138 n)). Qed.
Lemma lem2539140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539141 : term229 = term230.
Proof. exact (MK_COMB (@lem2539140) (@lem2539122)). Qed.
Lemma lem2539142 (n : int) : (term132 n) = (term231 n).
Proof. exact (MK_COMB (@lem2539141) (@lem2539139 n)). Qed.
Lemma lem2539143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539144 (n : int) : (term135 n) = (term232 n).
Proof. exact (MK_COMB (@lem2539143) (@lem2539095 n)). Qed.
Lemma lem2539145 (n : int) : (term137 n) = (term233 n).
Proof. exact (MK_COMB (@lem2539144 n) (@lem2539142 n)). Qed.
Lemma lem2539146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2539147 (n : int) : (term141 n) = (term234 n).
Proof. exact (MK_COMB (@lem2539146) (@lem2539012 n)). Qed.
Lemma lem2539148 (n : int) : (term143 n) = (term235 n).
Proof. exact (MK_COMB (@lem2539147 n) (@lem2539145 n)). Qed.
Lemma lem2539149 (n : int) : (term144 n) = (term235 n).
Proof. exact (TRANS (@lem2538965 n) (@lem2539148 n)). Qed.
Lemma lem2539153 (t : Prop) : (term236 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2539209 (n : int) : (term237 n) = (term235 n).
Proof. exact (@lem2539153 (term235 n)). Qed.
Lemma lem2539210 (n : int) : (term167 n) = (term238 n).
Proof. exact (@lem1988287 term166 (term162 n)). Qed.
Lemma lem2539222 (n : int) : (term239 n) = (term240 n).
Proof. exact (@lem1982792 term166 (term162 n)). Qed.
Lemma lem2539223 (n : int) : (term241 n) = (term242 n).
Proof. exact (@lem1982781 (real_of_int n) term243 term159). Qed.
Lemma lem2539225 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2539226 : term159 = term245.
Proof. exact (@lem2539225 term160). Qed.
Lemma lem2539228 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2539229 : term243 = term248.
Proof. exact (@lem2539228 term160). Qed.
Lemma lem2539230 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539231 : term249 = term250.
Proof. exact (MK_COMB (@lem2539230) (@lem2539229)). Qed.
Lemma lem2539232 : term251 = term252.
Proof. exact (MK_COMB (@lem2539231) (@lem2539226)). Qed.
Lemma lem2539233 : term252 = term253.
Proof. exact (@lem1981613 term243 term159 term159 term159). Qed.
Lemma lem2539235 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539236 : term256 = term257.
Proof. exact (@lem2539235 term160 term160). Qed.
Lemma lem2539237 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539238 : term259 = term160.
Proof. exact (EQ_MP (@lem2539237) (@lem940073)). Qed.
Lemma lem2539239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539240 : term257 = term159.
Proof. exact (MK_COMB (@lem2539239) (@lem2539238)). Qed.
Lemma lem2539241 : term256 = term159.
Proof. exact (TRANS (@lem2539236) (@lem2539240)). Qed.
Lemma lem2539243 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2539244 : term251 = term262.
Proof. exact (@lem2539243 term160 term160). Qed.
Lemma lem2539245 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539246 : term259 = term160.
Proof. exact (EQ_MP (@lem2539245) (@lem940073)). Qed.
Lemma lem2539247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539248 : term257 = term159.
Proof. exact (MK_COMB (@lem2539247) (@lem2539246)). Qed.
Lemma lem2539249 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2539250 : term262 = term243.
Proof. exact (MK_COMB (@lem2539249) (@lem2539248)). Qed.
Lemma lem2539251 : term251 = term243.
Proof. exact (TRANS (@lem2539244) (@lem2539250)). Qed.
Lemma lem2539252 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2539253 : term263 = term264.
Proof. exact (MK_COMB (@lem2539252) (@lem2539251)). Qed.
Lemma lem2539254 : term253 = term248.
Proof. exact (MK_COMB (@lem2539253) (@lem2539241)). Qed.
Lemma lem2539255 : term252 = term248.
Proof. exact (TRANS (@lem2539233) (@lem2539254)). Qed.
Lemma lem2539256 : term251 = term248.
Proof. exact (TRANS (@lem2539232) (@lem2539255)). Qed.
Lemma lem2539258 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2539259 : term248 = term243.
Proof. exact (@lem2539258 term243). Qed.
Lemma lem2539260 : term251 = term243.
Proof. exact (TRANS (@lem2539256) (@lem2539259)). Qed.
Lemma lem2539263 (n : int) : (term266 n) = (term266 n).
Proof. exact (eq_refl (term266 n)). Qed.
Lemma lem2539264 (n : int) : (term242 n) = (term267 n).
Proof. exact (MK_COMB (@lem2539263 n) (@lem2539260)). Qed.
Lemma lem2539265 (n : int) : (term241 n) = (term267 n).
Proof. exact (TRANS (@lem2539223 n) (@lem2539264 n)). Qed.
Lemma lem2539266 : term176 = term176.
Proof. exact (eq_refl term176). Qed.
Lemma lem2539267 (n : int) : (term240 n) = (term268 n).
Proof. exact (MK_COMB (@lem2539266) (@lem2539265 n)). Qed.
Lemma lem2539268 (n : int) : (term268 n) = (term267 n).
Proof. exact (@lem1982721 (term267 n)). Qed.
Lemma lem2539269 (n : int) : (term240 n) = (term267 n).
Proof. exact (TRANS (@lem2539267 n) (@lem2539268 n)). Qed.
Lemma lem2539271 (n : int) : (term239 n) = (term267 n).
Proof. exact (TRANS (@lem2539222 n) (@lem2539269 n)). Qed.
Lemma lem2539272 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539273 (n : int) : (term269 n) = (term270 n).
Proof. exact (MK_COMB (@lem2539272) (@lem2539271 n)). Qed.
Lemma lem2539274 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539275 (n : int) : (term238 n) = (term271 n).
Proof. exact (MK_COMB (@lem2539273 n) (@lem2539274)). Qed.
Lemma lem2539276 (n : int) : (term167 n) = (term271 n).
Proof. exact (TRANS (@lem2539210 n) (@lem2539275 n)). Qed.
Lemma lem2539277 (n : int) : (term180 n) = (term272 n).
Proof. exact (@lem1988287 (real_of_int n) term177). Qed.
Lemma lem2539284 : term177 = term159.
Proof. exact (@lem1982721 term159). Qed.
Lemma lem2539287 (n : int) : (term273 n) = (term273 n).
Proof. exact (eq_refl (term273 n)). Qed.
Lemma lem2539288 (n : int) : (term274 n) = (term275 n).
Proof. exact (MK_COMB (@lem2539287 n) (@lem2539284)). Qed.
Lemma lem2539289 (n : int) : (term275 n) = (term276 n).
Proof. exact (@lem1982792 (real_of_int n) term159). Qed.
Lemma lem2539291 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2539292 : term159 = term245.
Proof. exact (@lem2539291 term160). Qed.
Lemma lem2539294 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2539295 : term243 = term248.
Proof. exact (@lem2539294 term160). Qed.
Lemma lem2539296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539297 : term249 = term250.
Proof. exact (MK_COMB (@lem2539296) (@lem2539295)). Qed.
Lemma lem2539298 : term251 = term252.
Proof. exact (MK_COMB (@lem2539297) (@lem2539292)). Qed.
Lemma lem2539299 : term252 = term253.
Proof. exact (@lem1981613 term243 term159 term159 term159). Qed.
Lemma lem2539301 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539302 : term256 = term257.
Proof. exact (@lem2539301 term160 term160). Qed.
Lemma lem2539303 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539304 : term259 = term160.
Proof. exact (EQ_MP (@lem2539303) (@lem940073)). Qed.
Lemma lem2539305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539306 : term257 = term159.
Proof. exact (MK_COMB (@lem2539305) (@lem2539304)). Qed.
Lemma lem2539307 : term256 = term159.
Proof. exact (TRANS (@lem2539302) (@lem2539306)). Qed.
Lemma lem2539309 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2539310 : term251 = term262.
Proof. exact (@lem2539309 term160 term160). Qed.
Lemma lem2539311 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539312 : term259 = term160.
Proof. exact (EQ_MP (@lem2539311) (@lem940073)). Qed.
Lemma lem2539313 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539314 : term257 = term159.
Proof. exact (MK_COMB (@lem2539313) (@lem2539312)). Qed.
Lemma lem2539315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2539316 : term262 = term243.
Proof. exact (MK_COMB (@lem2539315) (@lem2539314)). Qed.
Lemma lem2539317 : term251 = term243.
Proof. exact (TRANS (@lem2539310) (@lem2539316)). Qed.
Lemma lem2539318 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2539319 : term263 = term264.
Proof. exact (MK_COMB (@lem2539318) (@lem2539317)). Qed.
Lemma lem2539320 : term253 = term248.
Proof. exact (MK_COMB (@lem2539319) (@lem2539307)). Qed.
Lemma lem2539321 : term252 = term248.
Proof. exact (TRANS (@lem2539299) (@lem2539320)). Qed.
Lemma lem2539322 : term251 = term248.
Proof. exact (TRANS (@lem2539298) (@lem2539321)). Qed.
Lemma lem2539324 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2539325 : term248 = term243.
Proof. exact (@lem2539324 term243). Qed.
Lemma lem2539326 : term251 = term243.
Proof. exact (TRANS (@lem2539322) (@lem2539325)). Qed.
Lemma lem2539327 (n : int) : (term161 n) = (term161 n).
Proof. exact (eq_refl (term161 n)). Qed.
Lemma lem2539330 (n : int) : (term276 n) = (term277 n).
Proof. exact (MK_COMB (@lem2539327 n) (@lem2539326)). Qed.
Lemma lem2539331 (n : int) : (term275 n) = (term277 n).
Proof. exact (TRANS (@lem2539289 n) (@lem2539330 n)). Qed.
Lemma lem2539332 (n : int) : (term274 n) = (term277 n).
Proof. exact (TRANS (@lem2539288 n) (@lem2539331 n)). Qed.
Lemma lem2539333 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539334 (n : int) : (term278 n) = (term279 n).
Proof. exact (MK_COMB (@lem2539333) (@lem2539332 n)). Qed.
Lemma lem2539335 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539336 (n : int) : (term272 n) = (term280 n).
Proof. exact (MK_COMB (@lem2539334 n) (@lem2539335)). Qed.
Lemma lem2539337 (n : int) : (term180 n) = (term280 n).
Proof. exact (TRANS (@lem2539277 n) (@lem2539336 n)). Qed.
Lemma lem2539338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539339 (n : int) : (term169 n) = (term281 n).
Proof. exact (MK_COMB (@lem2539338) (@lem2539276 n)). Qed.
Lemma lem2539340 (n : int) : (term181 n) = (term282 n).
Proof. exact (MK_COMB (@lem2539339 n) (@lem2539337 n)). Qed.
Lemma lem2539341 (n : int) : (term199 n) = (term283 n).
Proof. exact (@lem1988287 (term198 n) (term162 n)). Qed.
Lemma lem2539348 (n : int) : (term162 n) = (term162 n).
Proof. exact (eq_refl (term162 n)). Qed.
Lemma lem2539349 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539356 (n : int) : (term195 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2539357 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539358 (n : int) : (term197 n) = (term161 n).
Proof. exact (MK_COMB (@lem2539357) (@lem2539356 n)). Qed.
Lemma lem2539359 (n : int) : (term198 n) = (term284 n).
Proof. exact (MK_COMB (@lem2539358 n) (@lem2539349)). Qed.
Lemma lem2539360 (n : int) : (term284 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2539361 (n : int) : (term198 n) = (real_of_int n).
Proof. exact (TRANS (@lem2539359 n) (@lem2539360 n)). Qed.
Lemma lem2539362 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2539363 (n : int) : (term285 n) = (term273 n).
Proof. exact (MK_COMB (@lem2539362) (@lem2539361 n)). Qed.
Lemma lem2539364 (n : int) : (term286 n) = (term287 n).
Proof. exact (MK_COMB (@lem2539363 n) (@lem2539348 n)). Qed.
Lemma lem2539365 (n : int) : (term287 n) = (term288 n).
Proof. exact (@lem1982792 (real_of_int n) (term162 n)). Qed.
Lemma lem2539366 (n : int) : (term241 n) = (term242 n).
Proof. exact (@lem1982781 (real_of_int n) term243 term159). Qed.
Lemma lem2539368 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2539369 : term159 = term245.
Proof. exact (@lem2539368 term160). Qed.
Lemma lem2539371 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2539372 : term243 = term248.
Proof. exact (@lem2539371 term160). Qed.
Lemma lem2539373 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539374 : term249 = term250.
Proof. exact (MK_COMB (@lem2539373) (@lem2539372)). Qed.
Lemma lem2539375 : term251 = term252.
Proof. exact (MK_COMB (@lem2539374) (@lem2539369)). Qed.
Lemma lem2539376 : term252 = term253.
Proof. exact (@lem1981613 term243 term159 term159 term159). Qed.
Lemma lem2539378 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539379 : term256 = term257.
Proof. exact (@lem2539378 term160 term160). Qed.
Lemma lem2539380 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539381 : term259 = term160.
Proof. exact (EQ_MP (@lem2539380) (@lem940073)). Qed.
Lemma lem2539382 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539383 : term257 = term159.
Proof. exact (MK_COMB (@lem2539382) (@lem2539381)). Qed.
Lemma lem2539384 : term256 = term159.
Proof. exact (TRANS (@lem2539379) (@lem2539383)). Qed.
Lemma lem2539386 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2539387 : term251 = term262.
Proof. exact (@lem2539386 term160 term160). Qed.
Lemma lem2539388 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539389 : term259 = term160.
Proof. exact (EQ_MP (@lem2539388) (@lem940073)). Qed.
Lemma lem2539390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539391 : term257 = term159.
Proof. exact (MK_COMB (@lem2539390) (@lem2539389)). Qed.
Lemma lem2539392 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2539393 : term262 = term243.
Proof. exact (MK_COMB (@lem2539392) (@lem2539391)). Qed.
Lemma lem2539394 : term251 = term243.
Proof. exact (TRANS (@lem2539387) (@lem2539393)). Qed.
Lemma lem2539395 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2539396 : term263 = term264.
Proof. exact (MK_COMB (@lem2539395) (@lem2539394)). Qed.
Lemma lem2539397 : term253 = term248.
Proof. exact (MK_COMB (@lem2539396) (@lem2539384)). Qed.
Lemma lem2539398 : term252 = term248.
Proof. exact (TRANS (@lem2539376) (@lem2539397)). Qed.
Lemma lem2539399 : term251 = term248.
Proof. exact (TRANS (@lem2539375) (@lem2539398)). Qed.
Lemma lem2539401 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2539402 : term248 = term243.
Proof. exact (@lem2539401 term243). Qed.
Lemma lem2539403 : term251 = term243.
Proof. exact (TRANS (@lem2539399) (@lem2539402)). Qed.
Lemma lem2539406 (n : int) : (term266 n) = (term266 n).
Proof. exact (eq_refl (term266 n)). Qed.
Lemma lem2539407 (n : int) : (term242 n) = (term267 n).
Proof. exact (MK_COMB (@lem2539406 n) (@lem2539403)). Qed.
Lemma lem2539408 (n : int) : (term241 n) = (term267 n).
Proof. exact (TRANS (@lem2539366 n) (@lem2539407 n)). Qed.
Lemma lem2539409 (n : int) : (term161 n) = (term161 n).
Proof. exact (eq_refl (term161 n)). Qed.
Lemma lem2539410 (n : int) : (term288 n) = (term289 n).
Proof. exact (MK_COMB (@lem2539409 n) (@lem2539408 n)). Qed.
Lemma lem2539411 (n : int) : (term289 n) = (term290 n).
Proof. exact (@lem1982763 (real_of_int n) (term291 n) term243). Qed.
Lemma lem2539412 (n : int) : (term292 n) = (term293 n).
Proof. exact (@lem1982715 term243 (real_of_int n)). Qed.
Lemma lem2539414 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2539415 : term159 = term245.
Proof. exact (@lem2539414 term160). Qed.
Lemma lem2539417 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2539418 : term243 = term248.
Proof. exact (@lem2539417 term160). Qed.
Lemma lem2539419 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539420 : term294 = term295.
Proof. exact (MK_COMB (@lem2539419) (@lem2539418)). Qed.
Lemma lem2539421 : term296 = term297.
Proof. exact (MK_COMB (@lem2539420) (@lem2539415)). Qed.
Lemma lem2539422 : term298.
Proof. exact (@lem1981473 term243 term159 term159 term159 term166 term159). Qed.
Lemma lem2539424 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2539425 : term300 = term301.
Proof. exact (@lem2539424 (NUMERAL 0) term160). Qed.
Lemma lem2539426 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2539427 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2539428 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2539427 h1) (fun h1 : term301 = True => @lem2539426)). Qed.
Lemma lem2539429 : term301 = True.
Proof. exact (EQ_MP (@lem2539428) (@lem2539426)). Qed.
Lemma lem2539430 : term300 = True.
Proof. exact (TRANS (@lem2539425) (@lem2539429)). Qed.
Lemma lem2539431 : True = term300.
Proof. exact (SYM (@lem2539430)). Qed.
Lemma lem2539432 : term300.
Proof. exact (EQ_MP (@lem2539431) (@lem0)). Qed.
Lemma lem2539433 : term303.
Proof. exact (@lem2539422 (@lem2539432)). Qed.
Lemma lem2539435 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2539436 : term300 = term301.
Proof. exact (@lem2539435 (NUMERAL 0) term160). Qed.
Lemma lem2539437 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2539438 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2539439 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2539438 h1) (fun h1 : term301 = True => @lem2539437)). Qed.
Lemma lem2539440 : term301 = True.
Proof. exact (EQ_MP (@lem2539439) (@lem2539437)). Qed.
Lemma lem2539441 : term300 = True.
Proof. exact (TRANS (@lem2539436) (@lem2539440)). Qed.
Lemma lem2539442 : True = term300.
Proof. exact (SYM (@lem2539441)). Qed.
Lemma lem2539443 : term300.
Proof. exact (EQ_MP (@lem2539442) (@lem0)). Qed.
Lemma lem2539444 : term304.
Proof. exact (@lem2539433 (@lem2539443)). Qed.
Lemma lem2539446 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2539447 : term300 = term301.
Proof. exact (@lem2539446 (NUMERAL 0) term160). Qed.
Lemma lem2539448 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2539449 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2539450 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2539449 h1) (fun h1 : term301 = True => @lem2539448)). Qed.
Lemma lem2539451 : term301 = True.
Proof. exact (EQ_MP (@lem2539450) (@lem2539448)). Qed.
Lemma lem2539452 : term300 = True.
Proof. exact (TRANS (@lem2539447) (@lem2539451)). Qed.
Lemma lem2539453 : True = term300.
Proof. exact (SYM (@lem2539452)). Qed.
Lemma lem2539454 : term300.
Proof. exact (EQ_MP (@lem2539453) (@lem0)). Qed.
Lemma lem2539455 : term305.
Proof. exact (@lem2539444 (@lem2539454)). Qed.
Lemma lem2539457 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539458 : term256 = term257.
Proof. exact (@lem2539457 term160 term160). Qed.
Lemma lem2539459 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539460 : term259 = term160.
Proof. exact (EQ_MP (@lem2539459) (@lem940073)). Qed.
Lemma lem2539461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539462 : term257 = term159.
Proof. exact (MK_COMB (@lem2539461) (@lem2539460)). Qed.
Lemma lem2539463 : term256 = term159.
Proof. exact (TRANS (@lem2539458) (@lem2539462)). Qed.
Lemma lem2539465 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2539466 : term251 = term262.
Proof. exact (@lem2539465 term160 term160). Qed.
Lemma lem2539467 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539468 : term259 = term160.
Proof. exact (EQ_MP (@lem2539467) (@lem940073)). Qed.
Lemma lem2539469 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539470 : term257 = term159.
Proof. exact (MK_COMB (@lem2539469) (@lem2539468)). Qed.
Lemma lem2539471 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2539472 : term262 = term243.
Proof. exact (MK_COMB (@lem2539471) (@lem2539470)). Qed.
Lemma lem2539473 : term251 = term243.
Proof. exact (TRANS (@lem2539466) (@lem2539472)). Qed.
Lemma lem2539474 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539475 : term306 = term294.
Proof. exact (MK_COMB (@lem2539474) (@lem2539473)). Qed.
Lemma lem2539476 : term307 = term296.
Proof. exact (MK_COMB (@lem2539475) (@lem2539463)). Qed.
Lemma lem2539478 (m : nat) : (term308 m) = term166.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2539479 : term296 = term166.
Proof. exact (@lem2539478 term160). Qed.
Lemma lem2539480 : term307 = term166.
Proof. exact (TRANS (@lem2539476) (@lem2539479)). Qed.
Lemma lem2539481 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539482 : term309 = term310.
Proof. exact (MK_COMB (@lem2539481) (@lem2539480)). Qed.
Lemma lem2539483 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2539484 : term311 = term312.
Proof. exact (MK_COMB (@lem2539482) (@lem2539483)). Qed.
Lemma lem2539486 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2539487 : term312 = term166.
Proof. exact (@lem2539486 term160). Qed.
Lemma lem2539488 : term311 = term166.
Proof. exact (TRANS (@lem2539484) (@lem2539487)). Qed.
Lemma lem2539490 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539491 : term256 = term257.
Proof. exact (@lem2539490 term160 term160). Qed.
Lemma lem2539492 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539493 : term259 = term160.
Proof. exact (EQ_MP (@lem2539492) (@lem940073)). Qed.
Lemma lem2539494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539495 : term257 = term159.
Proof. exact (MK_COMB (@lem2539494) (@lem2539493)). Qed.
Lemma lem2539496 : term256 = term159.
Proof. exact (TRANS (@lem2539491) (@lem2539495)). Qed.
Lemma lem2539497 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem2539498 : term314 = term312.
Proof. exact (MK_COMB (@lem2539497) (@lem2539496)). Qed.
Lemma lem2539500 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2539501 : term312 = term166.
Proof. exact (@lem2539500 term160). Qed.
Lemma lem2539502 : term314 = term166.
Proof. exact (TRANS (@lem2539498) (@lem2539501)). Qed.
Lemma lem2539503 : term166 = term314.
Proof. exact (SYM (@lem2539502)). Qed.
Lemma lem2539504 : term311 = term314.
Proof. exact (TRANS (@lem2539488) (@lem2539503)). Qed.
Lemma lem2539505 : term297 = term315.
Proof. exact (@lem2539455 (@lem2539504)). Qed.
Lemma lem2539506 : term296 = term315.
Proof. exact (TRANS (@lem2539421) (@lem2539505)). Qed.
Lemma lem2539508 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2539509 : term315 = term166.
Proof. exact (@lem2539508 term166). Qed.
Lemma lem2539510 : term296 = term166.
Proof. exact (TRANS (@lem2539506) (@lem2539509)). Qed.
Lemma lem2539511 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539512 : term316 = term310.
Proof. exact (MK_COMB (@lem2539511) (@lem2539510)). Qed.
Lemma lem2539513 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2539514 (n : int) : (term293 n) = (term317 n).
Proof. exact (MK_COMB (@lem2539512) (@lem2539513 n)). Qed.
Lemma lem2539515 (n : int) : (term292 n) = (term317 n).
Proof. exact (TRANS (@lem2539412 n) (@lem2539514 n)). Qed.
Lemma lem2539516 (n : int) : (term317 n) = term166.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2539517 (n : int) : (term292 n) = term166.
Proof. exact (TRANS (@lem2539515 n) (@lem2539516 n)). Qed.
Lemma lem2539518 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539519 (n : int) : (term318 n) = term176.
Proof. exact (MK_COMB (@lem2539518) (@lem2539517 n)). Qed.
Lemma lem2539520 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem2539521 (n : int) : (term290 n) = term319.
Proof. exact (MK_COMB (@lem2539519 n) (@lem2539520)). Qed.
Lemma lem2539522 (n : int) : (term289 n) = term319.
Proof. exact (TRANS (@lem2539411 n) (@lem2539521 n)). Qed.
Lemma lem2539523 : term319 = term243.
Proof. exact (@lem1982721 term243). Qed.
Lemma lem2539524 (n : int) : (term289 n) = term243.
Proof. exact (TRANS (@lem2539522 n) (@lem2539523)). Qed.
Lemma lem2539525 (n : int) : (term288 n) = term243.
Proof. exact (TRANS (@lem2539410 n) (@lem2539524 n)). Qed.
Lemma lem2539526 (n : int) : (term287 n) = term243.
Proof. exact (TRANS (@lem2539365 n) (@lem2539525 n)). Qed.
Lemma lem2539527 (n : int) : (term286 n) = term243.
Proof. exact (TRANS (@lem2539364 n) (@lem2539526 n)). Qed.
Lemma lem2539528 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539529 (n : int) : (term320 n) = term321.
Proof. exact (MK_COMB (@lem2539528) (@lem2539527 n)). Qed.
Lemma lem2539530 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539531 (n : int) : (term283 n) = term322.
Proof. exact (MK_COMB (@lem2539529 n) (@lem2539530)). Qed.
Lemma lem2539532 (n : int) : (term199 n) = term322.
Proof. exact (TRANS (@lem2539341 n) (@lem2539531 n)). Qed.
Lemma lem2539533 (n : int) : (term212 n) = (term323 n).
Proof. exact (@lem1988287 (real_of_int n) (term209 n)). Qed.
Lemma lem2539534 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2539535 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539542 (n : int) : (term195 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2539543 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539544 (n : int) : (term197 n) = (term161 n).
Proof. exact (MK_COMB (@lem2539543) (@lem2539542 n)). Qed.
Lemma lem2539545 (n : int) : (term198 n) = (term284 n).
Proof. exact (MK_COMB (@lem2539544 n) (@lem2539535)). Qed.
Lemma lem2539546 (n : int) : (term284 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2539547 (n : int) : (term198 n) = (real_of_int n).
Proof. exact (TRANS (@lem2539545 n) (@lem2539546 n)). Qed.
Lemma lem2539548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539549 (n : int) : (term208 n) = (term161 n).
Proof. exact (MK_COMB (@lem2539548) (@lem2539547 n)). Qed.
Lemma lem2539552 (n : int) : (term209 n) = (term162 n).
Proof. exact (MK_COMB (@lem2539549 n) (@lem2539534)). Qed.
Lemma lem2539555 (n : int) : (term273 n) = (term273 n).
Proof. exact (eq_refl (term273 n)). Qed.
Lemma lem2539556 (n : int) : (term324 n) = (term287 n).
Proof. exact (MK_COMB (@lem2539555 n) (@lem2539552 n)). Qed.
Lemma lem2539557 (n : int) : (term287 n) = (term288 n).
Proof. exact (@lem1982792 (real_of_int n) (term162 n)). Qed.
Lemma lem2539558 (n : int) : (term241 n) = (term242 n).
Proof. exact (@lem1982781 (real_of_int n) term243 term159). Qed.
Lemma lem2539560 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2539561 : term159 = term245.
Proof. exact (@lem2539560 term160). Qed.
Lemma lem2539563 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2539564 : term243 = term248.
Proof. exact (@lem2539563 term160). Qed.
Lemma lem2539565 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539566 : term249 = term250.
Proof. exact (MK_COMB (@lem2539565) (@lem2539564)). Qed.
Lemma lem2539567 : term251 = term252.
Proof. exact (MK_COMB (@lem2539566) (@lem2539561)). Qed.
Lemma lem2539568 : term252 = term253.
Proof. exact (@lem1981613 term243 term159 term159 term159). Qed.
Lemma lem2539570 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539571 : term256 = term257.
Proof. exact (@lem2539570 term160 term160). Qed.
Lemma lem2539572 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539573 : term259 = term160.
Proof. exact (EQ_MP (@lem2539572) (@lem940073)). Qed.
Lemma lem2539574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539575 : term257 = term159.
Proof. exact (MK_COMB (@lem2539574) (@lem2539573)). Qed.
Lemma lem2539576 : term256 = term159.
Proof. exact (TRANS (@lem2539571) (@lem2539575)). Qed.
Lemma lem2539578 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2539579 : term251 = term262.
Proof. exact (@lem2539578 term160 term160). Qed.
Lemma lem2539580 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539581 : term259 = term160.
Proof. exact (EQ_MP (@lem2539580) (@lem940073)). Qed.
Lemma lem2539582 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539583 : term257 = term159.
Proof. exact (MK_COMB (@lem2539582) (@lem2539581)). Qed.
Lemma lem2539584 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2539585 : term262 = term243.
Proof. exact (MK_COMB (@lem2539584) (@lem2539583)). Qed.
Lemma lem2539586 : term251 = term243.
Proof. exact (TRANS (@lem2539579) (@lem2539585)). Qed.
Lemma lem2539587 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2539588 : term263 = term264.
Proof. exact (MK_COMB (@lem2539587) (@lem2539586)). Qed.
Lemma lem2539589 : term253 = term248.
Proof. exact (MK_COMB (@lem2539588) (@lem2539576)). Qed.
Lemma lem2539590 : term252 = term248.
Proof. exact (TRANS (@lem2539568) (@lem2539589)). Qed.
Lemma lem2539591 : term251 = term248.
Proof. exact (TRANS (@lem2539567) (@lem2539590)). Qed.
Lemma lem2539593 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2539594 : term248 = term243.
Proof. exact (@lem2539593 term243). Qed.
Lemma lem2539595 : term251 = term243.
Proof. exact (TRANS (@lem2539591) (@lem2539594)). Qed.
Lemma lem2539598 (n : int) : (term266 n) = (term266 n).
Proof. exact (eq_refl (term266 n)). Qed.
Lemma lem2539599 (n : int) : (term242 n) = (term267 n).
Proof. exact (MK_COMB (@lem2539598 n) (@lem2539595)). Qed.
Lemma lem2539600 (n : int) : (term241 n) = (term267 n).
Proof. exact (TRANS (@lem2539558 n) (@lem2539599 n)). Qed.
Lemma lem2539601 (n : int) : (term161 n) = (term161 n).
Proof. exact (eq_refl (term161 n)). Qed.
Lemma lem2539602 (n : int) : (term288 n) = (term289 n).
Proof. exact (MK_COMB (@lem2539601 n) (@lem2539600 n)). Qed.
Lemma lem2539603 (n : int) : (term289 n) = (term290 n).
Proof. exact (@lem1982763 (real_of_int n) (term291 n) term243). Qed.
Lemma lem2539604 (n : int) : (term292 n) = (term293 n).
Proof. exact (@lem1982715 term243 (real_of_int n)). Qed.
Lemma lem2539606 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2539607 : term159 = term245.
Proof. exact (@lem2539606 term160). Qed.
Lemma lem2539609 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2539610 : term243 = term248.
Proof. exact (@lem2539609 term160). Qed.
Lemma lem2539611 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539612 : term294 = term295.
Proof. exact (MK_COMB (@lem2539611) (@lem2539610)). Qed.
Lemma lem2539613 : term296 = term297.
Proof. exact (MK_COMB (@lem2539612) (@lem2539607)). Qed.
Lemma lem2539614 : term298.
Proof. exact (@lem1981473 term243 term159 term159 term159 term166 term159). Qed.
Lemma lem2539616 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2539617 : term300 = term301.
Proof. exact (@lem2539616 (NUMERAL 0) term160). Qed.
Lemma lem2539618 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2539619 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2539620 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2539619 h1) (fun h1 : term301 = True => @lem2539618)). Qed.
Lemma lem2539621 : term301 = True.
Proof. exact (EQ_MP (@lem2539620) (@lem2539618)). Qed.
Lemma lem2539622 : term300 = True.
Proof. exact (TRANS (@lem2539617) (@lem2539621)). Qed.
Lemma lem2539623 : True = term300.
Proof. exact (SYM (@lem2539622)). Qed.
Lemma lem2539624 : term300.
Proof. exact (EQ_MP (@lem2539623) (@lem0)). Qed.
Lemma lem2539625 : term303.
Proof. exact (@lem2539614 (@lem2539624)). Qed.
Lemma lem2539627 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2539628 : term300 = term301.
Proof. exact (@lem2539627 (NUMERAL 0) term160). Qed.
Lemma lem2539629 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2539630 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2539631 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2539630 h1) (fun h1 : term301 = True => @lem2539629)). Qed.
Lemma lem2539632 : term301 = True.
Proof. exact (EQ_MP (@lem2539631) (@lem2539629)). Qed.
Lemma lem2539633 : term300 = True.
Proof. exact (TRANS (@lem2539628) (@lem2539632)). Qed.
Lemma lem2539634 : True = term300.
Proof. exact (SYM (@lem2539633)). Qed.
Lemma lem2539635 : term300.
Proof. exact (EQ_MP (@lem2539634) (@lem0)). Qed.
Lemma lem2539636 : term304.
Proof. exact (@lem2539625 (@lem2539635)). Qed.
Lemma lem2539638 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2539639 : term300 = term301.
Proof. exact (@lem2539638 (NUMERAL 0) term160). Qed.
Lemma lem2539640 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2539641 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2539642 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2539641 h1) (fun h1 : term301 = True => @lem2539640)). Qed.
Lemma lem2539643 : term301 = True.
Proof. exact (EQ_MP (@lem2539642) (@lem2539640)). Qed.
Lemma lem2539644 : term300 = True.
Proof. exact (TRANS (@lem2539639) (@lem2539643)). Qed.
Lemma lem2539645 : True = term300.
Proof. exact (SYM (@lem2539644)). Qed.
Lemma lem2539646 : term300.
Proof. exact (EQ_MP (@lem2539645) (@lem0)). Qed.
Lemma lem2539647 : term305.
Proof. exact (@lem2539636 (@lem2539646)). Qed.
Lemma lem2539649 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539650 : term256 = term257.
Proof. exact (@lem2539649 term160 term160). Qed.
Lemma lem2539651 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539652 : term259 = term160.
Proof. exact (EQ_MP (@lem2539651) (@lem940073)). Qed.
Lemma lem2539653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539654 : term257 = term159.
Proof. exact (MK_COMB (@lem2539653) (@lem2539652)). Qed.
Lemma lem2539655 : term256 = term159.
Proof. exact (TRANS (@lem2539650) (@lem2539654)). Qed.
Lemma lem2539657 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2539658 : term251 = term262.
Proof. exact (@lem2539657 term160 term160). Qed.
Lemma lem2539659 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539660 : term259 = term160.
Proof. exact (EQ_MP (@lem2539659) (@lem940073)). Qed.
Lemma lem2539661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539662 : term257 = term159.
Proof. exact (MK_COMB (@lem2539661) (@lem2539660)). Qed.
Lemma lem2539663 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2539664 : term262 = term243.
Proof. exact (MK_COMB (@lem2539663) (@lem2539662)). Qed.
Lemma lem2539665 : term251 = term243.
Proof. exact (TRANS (@lem2539658) (@lem2539664)). Qed.
Lemma lem2539666 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539667 : term306 = term294.
Proof. exact (MK_COMB (@lem2539666) (@lem2539665)). Qed.
Lemma lem2539668 : term307 = term296.
Proof. exact (MK_COMB (@lem2539667) (@lem2539655)). Qed.
Lemma lem2539670 (m : nat) : (term308 m) = term166.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2539671 : term296 = term166.
Proof. exact (@lem2539670 term160). Qed.
Lemma lem2539672 : term307 = term166.
Proof. exact (TRANS (@lem2539668) (@lem2539671)). Qed.
Lemma lem2539673 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539674 : term309 = term310.
Proof. exact (MK_COMB (@lem2539673) (@lem2539672)). Qed.
Lemma lem2539675 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2539676 : term311 = term312.
Proof. exact (MK_COMB (@lem2539674) (@lem2539675)). Qed.
Lemma lem2539678 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2539679 : term312 = term166.
Proof. exact (@lem2539678 term160). Qed.
Lemma lem2539680 : term311 = term166.
Proof. exact (TRANS (@lem2539676) (@lem2539679)). Qed.
Lemma lem2539682 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539683 : term256 = term257.
Proof. exact (@lem2539682 term160 term160). Qed.
Lemma lem2539684 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539685 : term259 = term160.
Proof. exact (EQ_MP (@lem2539684) (@lem940073)). Qed.
Lemma lem2539686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539687 : term257 = term159.
Proof. exact (MK_COMB (@lem2539686) (@lem2539685)). Qed.
Lemma lem2539688 : term256 = term159.
Proof. exact (TRANS (@lem2539683) (@lem2539687)). Qed.
Lemma lem2539689 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem2539690 : term314 = term312.
Proof. exact (MK_COMB (@lem2539689) (@lem2539688)). Qed.
Lemma lem2539692 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2539693 : term312 = term166.
Proof. exact (@lem2539692 term160). Qed.
Lemma lem2539694 : term314 = term166.
Proof. exact (TRANS (@lem2539690) (@lem2539693)). Qed.
Lemma lem2539695 : term166 = term314.
Proof. exact (SYM (@lem2539694)). Qed.
Lemma lem2539696 : term311 = term314.
Proof. exact (TRANS (@lem2539680) (@lem2539695)). Qed.
Lemma lem2539697 : term297 = term315.
Proof. exact (@lem2539647 (@lem2539696)). Qed.
Lemma lem2539698 : term296 = term315.
Proof. exact (TRANS (@lem2539613) (@lem2539697)). Qed.
Lemma lem2539700 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2539701 : term315 = term166.
Proof. exact (@lem2539700 term166). Qed.
Lemma lem2539702 : term296 = term166.
Proof. exact (TRANS (@lem2539698) (@lem2539701)). Qed.
Lemma lem2539703 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539704 : term316 = term310.
Proof. exact (MK_COMB (@lem2539703) (@lem2539702)). Qed.
Lemma lem2539705 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2539706 (n : int) : (term293 n) = (term317 n).
Proof. exact (MK_COMB (@lem2539704) (@lem2539705 n)). Qed.
Lemma lem2539707 (n : int) : (term292 n) = (term317 n).
Proof. exact (TRANS (@lem2539604 n) (@lem2539706 n)). Qed.
Lemma lem2539708 (n : int) : (term317 n) = term166.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2539709 (n : int) : (term292 n) = term166.
Proof. exact (TRANS (@lem2539707 n) (@lem2539708 n)). Qed.
Lemma lem2539710 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2539711 (n : int) : (term318 n) = term176.
Proof. exact (MK_COMB (@lem2539710) (@lem2539709 n)). Qed.
Lemma lem2539712 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem2539713 (n : int) : (term290 n) = term319.
Proof. exact (MK_COMB (@lem2539711 n) (@lem2539712)). Qed.
Lemma lem2539714 (n : int) : (term289 n) = term319.
Proof. exact (TRANS (@lem2539603 n) (@lem2539713 n)). Qed.
Lemma lem2539715 : term319 = term243.
Proof. exact (@lem1982721 term243). Qed.
Lemma lem2539716 (n : int) : (term289 n) = term243.
Proof. exact (TRANS (@lem2539714 n) (@lem2539715)). Qed.
Lemma lem2539717 (n : int) : (term288 n) = term243.
Proof. exact (TRANS (@lem2539602 n) (@lem2539716 n)). Qed.
Lemma lem2539718 (n : int) : (term287 n) = term243.
Proof. exact (TRANS (@lem2539557 n) (@lem2539717 n)). Qed.
Lemma lem2539719 (n : int) : (term324 n) = term243.
Proof. exact (TRANS (@lem2539556 n) (@lem2539718 n)). Qed.
Lemma lem2539720 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539721 (n : int) : (term325 n) = term321.
Proof. exact (MK_COMB (@lem2539720) (@lem2539719 n)). Qed.
Lemma lem2539722 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539723 (n : int) : (term323 n) = term322.
Proof. exact (MK_COMB (@lem2539721 n) (@lem2539722)). Qed.
Lemma lem2539724 (n : int) : (term212 n) = term322.
Proof. exact (TRANS (@lem2539533 n) (@lem2539723 n)). Qed.
Lemma lem2539725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539726 (n : int) : (term201 n) = term326.
Proof. exact (MK_COMB (@lem2539725) (@lem2539532 n)). Qed.
Lemma lem2539727 (n : int) : (term213 n) = term327.
Proof. exact (MK_COMB (@lem2539726 n) (@lem2539724 n)). Qed.
Lemma lem2539728 : term219 = term328.
Proof. exact (@lem1988287 term166 term177). Qed.
Lemma lem2539735 : term177 = term159.
Proof. exact (@lem1982721 term159). Qed.
Lemma lem2539738 : term329 = term329.
Proof. exact (eq_refl term329). Qed.
Lemma lem2539739 : term330 = term331.
Proof. exact (MK_COMB (@lem2539738) (@lem2539735)). Qed.
Lemma lem2539740 : term331 = term332.
Proof. exact (@lem1982792 term166 term159). Qed.
Lemma lem2539742 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2539743 : term159 = term245.
Proof. exact (@lem2539742 term160). Qed.
Lemma lem2539745 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2539746 : term243 = term248.
Proof. exact (@lem2539745 term160). Qed.
Lemma lem2539747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2539748 : term249 = term250.
Proof. exact (MK_COMB (@lem2539747) (@lem2539746)). Qed.
Lemma lem2539749 : term251 = term252.
Proof. exact (MK_COMB (@lem2539748) (@lem2539743)). Qed.
Lemma lem2539750 : term252 = term253.
Proof. exact (@lem1981613 term243 term159 term159 term159). Qed.
Lemma lem2539752 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2539753 : term256 = term257.
Proof. exact (@lem2539752 term160 term160). Qed.
Lemma lem2539754 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539755 : term259 = term160.
Proof. exact (EQ_MP (@lem2539754) (@lem940073)). Qed.
Lemma lem2539756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539757 : term257 = term159.
Proof. exact (MK_COMB (@lem2539756) (@lem2539755)). Qed.
Lemma lem2539758 : term256 = term159.
Proof. exact (TRANS (@lem2539753) (@lem2539757)). Qed.
Lemma lem2539760 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2539761 : term251 = term262.
Proof. exact (@lem2539760 term160 term160). Qed.
Lemma lem2539762 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2539763 : term259 = term160.
Proof. exact (EQ_MP (@lem2539762) (@lem940073)). Qed.
Lemma lem2539764 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2539765 : term257 = term159.
Proof. exact (MK_COMB (@lem2539764) (@lem2539763)). Qed.
Lemma lem2539766 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2539767 : term262 = term243.
Proof. exact (MK_COMB (@lem2539766) (@lem2539765)). Qed.
Lemma lem2539768 : term251 = term243.
Proof. exact (TRANS (@lem2539761) (@lem2539767)). Qed.
Lemma lem2539769 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2539770 : term263 = term264.
Proof. exact (MK_COMB (@lem2539769) (@lem2539768)). Qed.
Lemma lem2539771 : term253 = term248.
Proof. exact (MK_COMB (@lem2539770) (@lem2539758)). Qed.
Lemma lem2539772 : term252 = term248.
Proof. exact (TRANS (@lem2539750) (@lem2539771)). Qed.
Lemma lem2539773 : term251 = term248.
Proof. exact (TRANS (@lem2539749) (@lem2539772)). Qed.
Lemma lem2539775 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2539776 : term248 = term243.
Proof. exact (@lem2539775 term243). Qed.
Lemma lem2539777 : term251 = term243.
Proof. exact (TRANS (@lem2539773) (@lem2539776)). Qed.
Lemma lem2539778 : term176 = term176.
Proof. exact (eq_refl term176). Qed.
Lemma lem2539779 : term332 = term319.
Proof. exact (MK_COMB (@lem2539778) (@lem2539777)). Qed.
Lemma lem2539780 : term319 = term243.
Proof. exact (@lem1982721 term243). Qed.
Lemma lem2539781 : term332 = term243.
Proof. exact (TRANS (@lem2539779) (@lem2539780)). Qed.
Lemma lem2539782 : term331 = term243.
Proof. exact (TRANS (@lem2539740) (@lem2539781)). Qed.
Lemma lem2539783 : term330 = term243.
Proof. exact (TRANS (@lem2539739) (@lem2539782)). Qed.
Lemma lem2539784 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539785 : term333 = term321.
Proof. exact (MK_COMB (@lem2539784) (@lem2539783)). Qed.
Lemma lem2539786 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539787 : term328 = term322.
Proof. exact (MK_COMB (@lem2539785) (@lem2539786)). Qed.
Lemma lem2539788 : term219 = term322.
Proof. exact (TRANS (@lem2539728) (@lem2539787)). Qed.
Lemma lem2539789 (n : int) : (term228 n) = (term334 n).
Proof. exact (@lem1988287 term166 (term225 n)). Qed.
Lemma lem2539797 (n : int) : (term335 n) = (term336 n).
Proof. exact (@lem1982792 term166 (term225 n)). Qed.
Lemma lem2539802 (n : int) : (term336 n) = (term337 n).
Proof. exact (@lem1982721 (term337 n)). Qed.
Lemma lem2539804 (n : int) : (term335 n) = (term337 n).
Proof. exact (TRANS (@lem2539797 n) (@lem2539802 n)). Qed.
Lemma lem2539805 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539806 (n : int) : (term338 n) = (term339 n).
Proof. exact (MK_COMB (@lem2539805) (@lem2539804 n)). Qed.
Lemma lem2539807 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539808 (n : int) : (term334 n) = (term340 n).
Proof. exact (MK_COMB (@lem2539806 n) (@lem2539807)). Qed.
Lemma lem2539809 (n : int) : (term228 n) = (term340 n).
Proof. exact (TRANS (@lem2539789 n) (@lem2539808 n)). Qed.
Lemma lem2539810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539811 : term230 = term326.
Proof. exact (MK_COMB (@lem2539810) (@lem2539788)). Qed.
Lemma lem2539812 (n : int) : (term231 n) = (term341 n).
Proof. exact (MK_COMB (@lem2539811) (@lem2539809 n)). Qed.
Lemma lem2539813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539814 (n : int) : (term232 n) = term342.
Proof. exact (MK_COMB (@lem2539813) (@lem2539727 n)). Qed.
Lemma lem2539815 (n : int) : (term233 n) = (term343 n).
Proof. exact (MK_COMB (@lem2539814 n) (@lem2539812 n)). Qed.
Lemma lem2539816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2539817 (n : int) : (term234 n) = (term344 n).
Proof. exact (MK_COMB (@lem2539816) (@lem2539340 n)). Qed.
Lemma lem2539818 (n : int) : (term235 n) = (term345 n).
Proof. exact (MK_COMB (@lem2539817 n) (@lem2539815 n)). Qed.
Lemma lem2539825 (n : int) : (term237 n) = (term345 n).
Proof. exact (TRANS (@lem2539209 n) (@lem2539818 n)). Qed.
Lemma lem2539847 (n : int) : (term345 n) = (term346 n).
Proof. exact (@lem19158 term327 (term282 n) (term341 n)). Qed.
Lemma lem2539848 (n : int) : (term347 n) = (term348 n).
Proof. exact (@lem19158 term322 (term282 n) (term340 n)). Qed.
Lemma lem2539855 (n : int) : (term349 n) = (term350 n).
Proof. exact (@lem19367 (term271 n) (term280 n) (term340 n)). Qed.
Lemma lem2539862 (n : int) : (term351 n) = (term352 n).
Proof. exact (@lem19367 (term271 n) (term280 n) term322). Qed.
Lemma lem2539863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539864 (n : int) : (term353 n) = (term354 n).
Proof. exact (MK_COMB (@lem2539863) (@lem2539862 n)). Qed.
Lemma lem2539865 (n : int) : (term348 n) = (term355 n).
Proof. exact (MK_COMB (@lem2539864 n) (@lem2539855 n)). Qed.
Lemma lem2539866 (n : int) : (term347 n) = (term355 n).
Proof. exact (TRANS (@lem2539848 n) (@lem2539865 n)). Qed.
Lemma lem2539867 (n : int) : (term356 n) = (term357 n).
Proof. exact (@lem19158 term322 (term282 n) term322). Qed.
Lemma lem2539874 (n : int) : (term351 n) = (term352 n).
Proof. exact (@lem19367 (term271 n) (term280 n) term322). Qed.
Lemma lem2539881 (n : int) : (term351 n) = (term352 n).
Proof. exact (@lem19367 (term271 n) (term280 n) term322). Qed.
Lemma lem2539882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539883 (n : int) : (term353 n) = (term354 n).
Proof. exact (MK_COMB (@lem2539882) (@lem2539881 n)). Qed.
Lemma lem2539884 (n : int) : (term357 n) = (term358 n).
Proof. exact (MK_COMB (@lem2539883 n) (@lem2539874 n)). Qed.
Lemma lem2539885 (n : int) : (term356 n) = (term358 n).
Proof. exact (TRANS (@lem2539867 n) (@lem2539884 n)). Qed.
Lemma lem2539886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539887 (n : int) : (term359 n) = (term360 n).
Proof. exact (MK_COMB (@lem2539886) (@lem2539885 n)). Qed.
Lemma lem2539888 (n : int) : (term346 n) = (term361 n).
Proof. exact (MK_COMB (@lem2539887 n) (@lem2539866 n)). Qed.
Lemma lem2539890 (n : int) : (term345 n) = (term361 n).
Proof. exact (TRANS (@lem2539847 n) (@lem2539888 n)). Qed.
Lemma lem2539891 (n : int) : (term237 n) = (term361 n).
Proof. exact (TRANS (@lem2539825 n) (@lem2539890 n)). Qed.
Lemma lem2539923 (x : real) (r : real) : (term362 x r) = (term363 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2539924 (n : int) : (term340 n) = (term364 n).
Proof. exact (@lem2539923 (real_of_int n) term166). Qed.
Lemma lem2539931 (n : int) : (term195 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2539932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539933 (n : int) : (term365 n) = (term366 n).
Proof. exact (MK_COMB (@lem2539932) (@lem2539931 n)). Qed.
Lemma lem2539934 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539935 (n : int) : (term367 n) = (term368 n).
Proof. exact (MK_COMB (@lem2539933 n) (@lem2539934)). Qed.
Lemma lem2539948 (n : int) : (term369 n) = (term369 n).
Proof. exact (eq_refl (term369 n)). Qed.
Lemma lem2539949 (n : int) : (term364 n) = (term370 n).
Proof. exact (MK_COMB (@lem2539948 n) (@lem2539935 n)). Qed.
Lemma lem2539950 (n : int) : (term340 n) = (term370 n).
Proof. exact (TRANS (@lem2539924 n) (@lem2539949 n)). Qed.
Lemma lem2539951 (n : int) : (term371 n) = (term371 n).
Proof. exact (eq_refl (term371 n)). Qed.
Lemma lem2539954 (n : int) : (term372 n) = (term373 n).
Proof. exact (MK_COMB (@lem2539951 n) (@lem2539950 n)). Qed.
Lemma lem2539956 (x : real) (r : real) : (term362 x r) = (term363 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2539957 (n : int) : (term340 n) = (term364 n).
Proof. exact (@lem2539956 (real_of_int n) term166). Qed.
Lemma lem2539964 (n : int) : (term195 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2539965 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2539966 (n : int) : (term365 n) = (term366 n).
Proof. exact (MK_COMB (@lem2539965) (@lem2539964 n)). Qed.
Lemma lem2539967 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2539968 (n : int) : (term367 n) = (term368 n).
Proof. exact (MK_COMB (@lem2539966 n) (@lem2539967)). Qed.
Lemma lem2539981 (n : int) : (term369 n) = (term369 n).
Proof. exact (eq_refl (term369 n)). Qed.
Lemma lem2539982 (n : int) : (term364 n) = (term370 n).
Proof. exact (MK_COMB (@lem2539981 n) (@lem2539968 n)). Qed.
Lemma lem2539983 (n : int) : (term340 n) = (term370 n).
Proof. exact (TRANS (@lem2539957 n) (@lem2539982 n)). Qed.
Lemma lem2539984 (n : int) : (term374 n) = (term374 n).
Proof. exact (eq_refl (term374 n)). Qed.
Lemma lem2539987 (n : int) : (term375 n) = (term376 n).
Proof. exact (MK_COMB (@lem2539984 n) (@lem2539983 n)). Qed.
Lemma lem2539988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2539989 (n : int) : (term377 n) = (term378 n).
Proof. exact (MK_COMB (@lem2539988) (@lem2539954 n)). Qed.
Lemma lem2539990 (n : int) : (term350 n) = (term379 n).
Proof. exact (MK_COMB (@lem2539989 n) (@lem2539987 n)). Qed.
Lemma lem2539992 (n : int) : (term354 n) = (term354 n).
Proof. exact (eq_refl (term354 n)). Qed.
Lemma lem2539993 (n : int) : (term355 n) = (term380 n).
Proof. exact (MK_COMB (@lem2539992 n) (@lem2539990 n)). Qed.
Lemma lem2539995 (n : int) : (term360 n) = (term360 n).
Proof. exact (eq_refl (term360 n)). Qed.
Lemma lem2539996 (n : int) : (term361 n) = (term381 n).
Proof. exact (MK_COMB (@lem2539995 n) (@lem2539993 n)). Qed.
Lemma lem2539997 (n : int) (h1 : term381 n) : term381 n.
Proof. exact (h1). Qed.
Lemma lem2539998 (n : int) (h1 : term358 n) : term358 n.
Proof. exact (h1). Qed.
Lemma lem2539999 (n : int) (h1 : term352 n) : term352 n.
Proof. exact (h1). Qed.
Lemma lem2540000 (n : int) (h1 : term382 n) : term382 n.
Proof. exact (h1). Qed.
Lemma lem2540001 (n : int) (h1 : term382 n) : term322.
Proof. exact (proj2 (@lem2540000 n h1)). Qed.
Lemma lem2540004 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2540005 : term322 = term383.
Proof. exact (@lem2540004 term166 term243). Qed.
Lemma lem2540007 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540008 : term243 = term248.
Proof. exact (@lem2540007 term160). Qed.
Lemma lem2540010 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540011 : term166 = term315.
Proof. exact (@lem2540010 (NUMERAL 0)). Qed.
Lemma lem2540012 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540013 : term384 = term385.
Proof. exact (MK_COMB (@lem2540012) (@lem2540011)). Qed.
Lemma lem2540014 : term383 = term386.
Proof. exact (MK_COMB (@lem2540013) (@lem2540008)). Qed.
Lemma lem2540015 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2540017 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540018 : term300 = term301.
Proof. exact (@lem2540017 (NUMERAL 0) term160). Qed.
Lemma lem2540019 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540020 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540021 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540020 h1) (fun h1 : term301 = True => @lem2540019)). Qed.
Lemma lem2540022 : term301 = True.
Proof. exact (EQ_MP (@lem2540021) (@lem2540019)). Qed.
Lemma lem2540023 : term300 = True.
Proof. exact (TRANS (@lem2540018) (@lem2540022)). Qed.
Lemma lem2540024 : True = term300.
Proof. exact (SYM (@lem2540023)). Qed.
Lemma lem2540025 : term300.
Proof. exact (EQ_MP (@lem2540024) (@lem0)). Qed.
Lemma lem2540026 : term388.
Proof. exact (@lem2540015 (@lem2540025)). Qed.
Lemma lem2540028 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540029 : term300 = term301.
Proof. exact (@lem2540028 (NUMERAL 0) term160). Qed.
Lemma lem2540030 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540031 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540032 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540031 h1) (fun h1 : term301 = True => @lem2540030)). Qed.
Lemma lem2540033 : term301 = True.
Proof. exact (EQ_MP (@lem2540032) (@lem2540030)). Qed.
Lemma lem2540034 : term300 = True.
Proof. exact (TRANS (@lem2540029) (@lem2540033)). Qed.
Lemma lem2540035 : True = term300.
Proof. exact (SYM (@lem2540034)). Qed.
Lemma lem2540036 : term300.
Proof. exact (EQ_MP (@lem2540035) (@lem0)). Qed.
Lemma lem2540037 : term386 = term389.
Proof. exact (@lem2540026 (@lem2540036)). Qed.
Lemma lem2540039 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540040 : term251 = term262.
Proof. exact (@lem2540039 term160 term160). Qed.
Lemma lem2540041 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540042 : term259 = term160.
Proof. exact (EQ_MP (@lem2540041) (@lem940073)). Qed.
Lemma lem2540043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540044 : term257 = term159.
Proof. exact (MK_COMB (@lem2540043) (@lem2540042)). Qed.
Lemma lem2540045 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540046 : term262 = term243.
Proof. exact (MK_COMB (@lem2540045) (@lem2540044)). Qed.
Lemma lem2540047 : term251 = term243.
Proof. exact (TRANS (@lem2540040) (@lem2540046)). Qed.
Lemma lem2540049 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540050 : term312 = term166.
Proof. exact (@lem2540049 term160). Qed.
Lemma lem2540051 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540052 : term390 = term384.
Proof. exact (MK_COMB (@lem2540051) (@lem2540050)). Qed.
Lemma lem2540053 : term389 = term383.
Proof. exact (MK_COMB (@lem2540052) (@lem2540047)). Qed.
Lemma lem2540055 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2540056 : term383 = term393.
Proof. exact (@lem2540055 (NUMERAL 0) term160). Qed.
Lemma lem2540057 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540058 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2540059 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540058 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2540057)). Qed.
Lemma lem2540060 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2540059) (@lem2540057)). Qed.
Lemma lem2540061 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2540062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2540063 : term394 = (and True).
Proof. exact (MK_COMB (@lem2540062) (@lem2540061)). Qed.
Lemma lem2540064 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2540063) (@lem2540060)). Qed.
Lemma lem2540066 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2540067 : term393 = False.
Proof. exact (TRANS (@lem2540064) (@lem2540066)). Qed.
Lemma lem2540068 : term383 = False.
Proof. exact (TRANS (@lem2540056) (@lem2540067)). Qed.
Lemma lem2540069 : term389 = False.
Proof. exact (TRANS (@lem2540053) (@lem2540068)). Qed.
Lemma lem2540070 : term386 = False.
Proof. exact (TRANS (@lem2540037) (@lem2540069)). Qed.
Lemma lem2540071 : term383 = False.
Proof. exact (TRANS (@lem2540014) (@lem2540070)). Qed.
Lemma lem2540072 : term322 = False.
Proof. exact (TRANS (@lem2540005) (@lem2540071)). Qed.
Lemma lem2540073 (n : int) (h1 : term382 n) : False.
Proof. exact (EQ_MP (@lem2540072) (@lem2540001 n h1)). Qed.
Lemma lem2540074 (n : int) (h1 : term395 n) : term395 n.
Proof. exact (h1). Qed.
Lemma lem2540075 (n : int) (h1 : term395 n) : term322.
Proof. exact (proj2 (@lem2540074 n h1)). Qed.
Lemma lem2540078 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2540079 : term322 = term383.
Proof. exact (@lem2540078 term166 term243). Qed.
Lemma lem2540081 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540082 : term243 = term248.
Proof. exact (@lem2540081 term160). Qed.
Lemma lem2540084 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540085 : term166 = term315.
Proof. exact (@lem2540084 (NUMERAL 0)). Qed.
Lemma lem2540086 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540087 : term384 = term385.
Proof. exact (MK_COMB (@lem2540086) (@lem2540085)). Qed.
Lemma lem2540088 : term383 = term386.
Proof. exact (MK_COMB (@lem2540087) (@lem2540082)). Qed.
Lemma lem2540089 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2540091 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540092 : term300 = term301.
Proof. exact (@lem2540091 (NUMERAL 0) term160). Qed.
Lemma lem2540093 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540094 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540095 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540094 h1) (fun h1 : term301 = True => @lem2540093)). Qed.
Lemma lem2540096 : term301 = True.
Proof. exact (EQ_MP (@lem2540095) (@lem2540093)). Qed.
Lemma lem2540097 : term300 = True.
Proof. exact (TRANS (@lem2540092) (@lem2540096)). Qed.
Lemma lem2540098 : True = term300.
Proof. exact (SYM (@lem2540097)). Qed.
Lemma lem2540099 : term300.
Proof. exact (EQ_MP (@lem2540098) (@lem0)). Qed.
Lemma lem2540100 : term388.
Proof. exact (@lem2540089 (@lem2540099)). Qed.
Lemma lem2540102 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540103 : term300 = term301.
Proof. exact (@lem2540102 (NUMERAL 0) term160). Qed.
Lemma lem2540104 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540105 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540106 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540105 h1) (fun h1 : term301 = True => @lem2540104)). Qed.
Lemma lem2540107 : term301 = True.
Proof. exact (EQ_MP (@lem2540106) (@lem2540104)). Qed.
Lemma lem2540108 : term300 = True.
Proof. exact (TRANS (@lem2540103) (@lem2540107)). Qed.
Lemma lem2540109 : True = term300.
Proof. exact (SYM (@lem2540108)). Qed.
Lemma lem2540110 : term300.
Proof. exact (EQ_MP (@lem2540109) (@lem0)). Qed.
Lemma lem2540111 : term386 = term389.
Proof. exact (@lem2540100 (@lem2540110)). Qed.
Lemma lem2540113 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540114 : term251 = term262.
Proof. exact (@lem2540113 term160 term160). Qed.
Lemma lem2540115 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540116 : term259 = term160.
Proof. exact (EQ_MP (@lem2540115) (@lem940073)). Qed.
Lemma lem2540117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540118 : term257 = term159.
Proof. exact (MK_COMB (@lem2540117) (@lem2540116)). Qed.
Lemma lem2540119 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540120 : term262 = term243.
Proof. exact (MK_COMB (@lem2540119) (@lem2540118)). Qed.
Lemma lem2540121 : term251 = term243.
Proof. exact (TRANS (@lem2540114) (@lem2540120)). Qed.
Lemma lem2540123 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540124 : term312 = term166.
Proof. exact (@lem2540123 term160). Qed.
Lemma lem2540125 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540126 : term390 = term384.
Proof. exact (MK_COMB (@lem2540125) (@lem2540124)). Qed.
Lemma lem2540127 : term389 = term383.
Proof. exact (MK_COMB (@lem2540126) (@lem2540121)). Qed.
Lemma lem2540129 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2540130 : term383 = term393.
Proof. exact (@lem2540129 (NUMERAL 0) term160). Qed.
Lemma lem2540131 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540132 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2540133 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540132 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2540131)). Qed.
Lemma lem2540134 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2540133) (@lem2540131)). Qed.
Lemma lem2540135 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2540136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2540137 : term394 = (and True).
Proof. exact (MK_COMB (@lem2540136) (@lem2540135)). Qed.
Lemma lem2540138 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2540137) (@lem2540134)). Qed.
Lemma lem2540140 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2540141 : term393 = False.
Proof. exact (TRANS (@lem2540138) (@lem2540140)). Qed.
Lemma lem2540142 : term383 = False.
Proof. exact (TRANS (@lem2540130) (@lem2540141)). Qed.
Lemma lem2540143 : term389 = False.
Proof. exact (TRANS (@lem2540127) (@lem2540142)). Qed.
Lemma lem2540144 : term386 = False.
Proof. exact (TRANS (@lem2540111) (@lem2540143)). Qed.
Lemma lem2540145 : term383 = False.
Proof. exact (TRANS (@lem2540088) (@lem2540144)). Qed.
Lemma lem2540146 : term322 = False.
Proof. exact (TRANS (@lem2540079) (@lem2540145)). Qed.
Lemma lem2540147 (n : int) (h1 : term395 n) : False.
Proof. exact (EQ_MP (@lem2540146) (@lem2540075 n h1)). Qed.
Lemma lem2540148 (n : int) (h1 : term352 n) : False.
Proof. exact (or_elim (@lem2539999 n h1) (fun h0 : term382 n => @lem2540073 n h0) (fun h0 : term395 n => @lem2540147 n h0)). Qed.
Lemma lem2540149 (n : int) (h1 : term352 n) : term352 n.
Proof. exact (h1). Qed.
Lemma lem2540150 (n : int) (h1 : term382 n) : term382 n.
Proof. exact (h1). Qed.
Lemma lem2540151 (n : int) (h1 : term382 n) : term322.
Proof. exact (proj2 (@lem2540150 n h1)). Qed.
Lemma lem2540154 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2540155 : term322 = term383.
Proof. exact (@lem2540154 term166 term243). Qed.
Lemma lem2540157 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540158 : term243 = term248.
Proof. exact (@lem2540157 term160). Qed.
Lemma lem2540160 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540161 : term166 = term315.
Proof. exact (@lem2540160 (NUMERAL 0)). Qed.
Lemma lem2540162 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540163 : term384 = term385.
Proof. exact (MK_COMB (@lem2540162) (@lem2540161)). Qed.
Lemma lem2540164 : term383 = term386.
Proof. exact (MK_COMB (@lem2540163) (@lem2540158)). Qed.
Lemma lem2540165 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2540167 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540168 : term300 = term301.
Proof. exact (@lem2540167 (NUMERAL 0) term160). Qed.
Lemma lem2540169 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540170 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540171 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540170 h1) (fun h1 : term301 = True => @lem2540169)). Qed.
Lemma lem2540172 : term301 = True.
Proof. exact (EQ_MP (@lem2540171) (@lem2540169)). Qed.
Lemma lem2540173 : term300 = True.
Proof. exact (TRANS (@lem2540168) (@lem2540172)). Qed.
Lemma lem2540174 : True = term300.
Proof. exact (SYM (@lem2540173)). Qed.
Lemma lem2540175 : term300.
Proof. exact (EQ_MP (@lem2540174) (@lem0)). Qed.
Lemma lem2540176 : term388.
Proof. exact (@lem2540165 (@lem2540175)). Qed.
Lemma lem2540178 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540179 : term300 = term301.
Proof. exact (@lem2540178 (NUMERAL 0) term160). Qed.
Lemma lem2540180 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540181 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540182 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540181 h1) (fun h1 : term301 = True => @lem2540180)). Qed.
Lemma lem2540183 : term301 = True.
Proof. exact (EQ_MP (@lem2540182) (@lem2540180)). Qed.
Lemma lem2540184 : term300 = True.
Proof. exact (TRANS (@lem2540179) (@lem2540183)). Qed.
Lemma lem2540185 : True = term300.
Proof. exact (SYM (@lem2540184)). Qed.
Lemma lem2540186 : term300.
Proof. exact (EQ_MP (@lem2540185) (@lem0)). Qed.
Lemma lem2540187 : term386 = term389.
Proof. exact (@lem2540176 (@lem2540186)). Qed.
Lemma lem2540189 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540190 : term251 = term262.
Proof. exact (@lem2540189 term160 term160). Qed.
Lemma lem2540191 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540192 : term259 = term160.
Proof. exact (EQ_MP (@lem2540191) (@lem940073)). Qed.
Lemma lem2540193 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540194 : term257 = term159.
Proof. exact (MK_COMB (@lem2540193) (@lem2540192)). Qed.
Lemma lem2540195 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540196 : term262 = term243.
Proof. exact (MK_COMB (@lem2540195) (@lem2540194)). Qed.
Lemma lem2540197 : term251 = term243.
Proof. exact (TRANS (@lem2540190) (@lem2540196)). Qed.
Lemma lem2540199 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540200 : term312 = term166.
Proof. exact (@lem2540199 term160). Qed.
Lemma lem2540201 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540202 : term390 = term384.
Proof. exact (MK_COMB (@lem2540201) (@lem2540200)). Qed.
Lemma lem2540203 : term389 = term383.
Proof. exact (MK_COMB (@lem2540202) (@lem2540197)). Qed.
Lemma lem2540205 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2540206 : term383 = term393.
Proof. exact (@lem2540205 (NUMERAL 0) term160). Qed.
Lemma lem2540207 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540208 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2540209 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540208 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2540207)). Qed.
Lemma lem2540210 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2540209) (@lem2540207)). Qed.
Lemma lem2540211 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2540212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2540213 : term394 = (and True).
Proof. exact (MK_COMB (@lem2540212) (@lem2540211)). Qed.
Lemma lem2540214 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2540213) (@lem2540210)). Qed.
Lemma lem2540216 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2540217 : term393 = False.
Proof. exact (TRANS (@lem2540214) (@lem2540216)). Qed.
Lemma lem2540218 : term383 = False.
Proof. exact (TRANS (@lem2540206) (@lem2540217)). Qed.
Lemma lem2540219 : term389 = False.
Proof. exact (TRANS (@lem2540203) (@lem2540218)). Qed.
Lemma lem2540220 : term386 = False.
Proof. exact (TRANS (@lem2540187) (@lem2540219)). Qed.
Lemma lem2540221 : term383 = False.
Proof. exact (TRANS (@lem2540164) (@lem2540220)). Qed.
Lemma lem2540222 : term322 = False.
Proof. exact (TRANS (@lem2540155) (@lem2540221)). Qed.
Lemma lem2540223 (n : int) (h1 : term382 n) : False.
Proof. exact (EQ_MP (@lem2540222) (@lem2540151 n h1)). Qed.
Lemma lem2540224 (n : int) (h1 : term395 n) : term395 n.
Proof. exact (h1). Qed.
Lemma lem2540225 (n : int) (h1 : term395 n) : term322.
Proof. exact (proj2 (@lem2540224 n h1)). Qed.
Lemma lem2540228 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2540229 : term322 = term383.
Proof. exact (@lem2540228 term166 term243). Qed.
Lemma lem2540231 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540232 : term243 = term248.
Proof. exact (@lem2540231 term160). Qed.
Lemma lem2540234 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540235 : term166 = term315.
Proof. exact (@lem2540234 (NUMERAL 0)). Qed.
Lemma lem2540236 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540237 : term384 = term385.
Proof. exact (MK_COMB (@lem2540236) (@lem2540235)). Qed.
Lemma lem2540238 : term383 = term386.
Proof. exact (MK_COMB (@lem2540237) (@lem2540232)). Qed.
Lemma lem2540239 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2540241 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540242 : term300 = term301.
Proof. exact (@lem2540241 (NUMERAL 0) term160). Qed.
Lemma lem2540243 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540244 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540245 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540244 h1) (fun h1 : term301 = True => @lem2540243)). Qed.
Lemma lem2540246 : term301 = True.
Proof. exact (EQ_MP (@lem2540245) (@lem2540243)). Qed.
Lemma lem2540247 : term300 = True.
Proof. exact (TRANS (@lem2540242) (@lem2540246)). Qed.
Lemma lem2540248 : True = term300.
Proof. exact (SYM (@lem2540247)). Qed.
Lemma lem2540249 : term300.
Proof. exact (EQ_MP (@lem2540248) (@lem0)). Qed.
Lemma lem2540250 : term388.
Proof. exact (@lem2540239 (@lem2540249)). Qed.
Lemma lem2540252 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540253 : term300 = term301.
Proof. exact (@lem2540252 (NUMERAL 0) term160). Qed.
Lemma lem2540254 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540255 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540256 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540255 h1) (fun h1 : term301 = True => @lem2540254)). Qed.
Lemma lem2540257 : term301 = True.
Proof. exact (EQ_MP (@lem2540256) (@lem2540254)). Qed.
Lemma lem2540258 : term300 = True.
Proof. exact (TRANS (@lem2540253) (@lem2540257)). Qed.
Lemma lem2540259 : True = term300.
Proof. exact (SYM (@lem2540258)). Qed.
Lemma lem2540260 : term300.
Proof. exact (EQ_MP (@lem2540259) (@lem0)). Qed.
Lemma lem2540261 : term386 = term389.
Proof. exact (@lem2540250 (@lem2540260)). Qed.
Lemma lem2540263 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540264 : term251 = term262.
Proof. exact (@lem2540263 term160 term160). Qed.
Lemma lem2540265 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540266 : term259 = term160.
Proof. exact (EQ_MP (@lem2540265) (@lem940073)). Qed.
Lemma lem2540267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540268 : term257 = term159.
Proof. exact (MK_COMB (@lem2540267) (@lem2540266)). Qed.
Lemma lem2540269 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540270 : term262 = term243.
Proof. exact (MK_COMB (@lem2540269) (@lem2540268)). Qed.
Lemma lem2540271 : term251 = term243.
Proof. exact (TRANS (@lem2540264) (@lem2540270)). Qed.
Lemma lem2540273 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540274 : term312 = term166.
Proof. exact (@lem2540273 term160). Qed.
Lemma lem2540275 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540276 : term390 = term384.
Proof. exact (MK_COMB (@lem2540275) (@lem2540274)). Qed.
Lemma lem2540277 : term389 = term383.
Proof. exact (MK_COMB (@lem2540276) (@lem2540271)). Qed.
Lemma lem2540279 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2540280 : term383 = term393.
Proof. exact (@lem2540279 (NUMERAL 0) term160). Qed.
Lemma lem2540281 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540282 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2540283 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540282 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2540281)). Qed.
Lemma lem2540284 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2540283) (@lem2540281)). Qed.
Lemma lem2540285 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2540286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2540287 : term394 = (and True).
Proof. exact (MK_COMB (@lem2540286) (@lem2540285)). Qed.
Lemma lem2540288 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2540287) (@lem2540284)). Qed.
Lemma lem2540290 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2540291 : term393 = False.
Proof. exact (TRANS (@lem2540288) (@lem2540290)). Qed.
Lemma lem2540292 : term383 = False.
Proof. exact (TRANS (@lem2540280) (@lem2540291)). Qed.
Lemma lem2540293 : term389 = False.
Proof. exact (TRANS (@lem2540277) (@lem2540292)). Qed.
Lemma lem2540294 : term386 = False.
Proof. exact (TRANS (@lem2540261) (@lem2540293)). Qed.
Lemma lem2540295 : term383 = False.
Proof. exact (TRANS (@lem2540238) (@lem2540294)). Qed.
Lemma lem2540296 : term322 = False.
Proof. exact (TRANS (@lem2540229) (@lem2540295)). Qed.
Lemma lem2540297 (n : int) (h1 : term395 n) : False.
Proof. exact (EQ_MP (@lem2540296) (@lem2540225 n h1)). Qed.
Lemma lem2540298 (n : int) (h1 : term352 n) : False.
Proof. exact (or_elim (@lem2540149 n h1) (fun h0 : term382 n => @lem2540223 n h0) (fun h0 : term395 n => @lem2540297 n h0)). Qed.
Lemma lem2540299 (n : int) (h1 : term358 n) : False.
Proof. exact (or_elim (@lem2539998 n h1) (fun h0 : term352 n => @lem2540148 n h0) (fun h0 : term352 n => @lem2540298 n h0)). Qed.
Lemma lem2540300 (n : int) (h1 : term380 n) : term380 n.
Proof. exact (h1). Qed.
Lemma lem2540301 (n : int) (h1 : term352 n) : term352 n.
Proof. exact (h1). Qed.
Lemma lem2540302 (n : int) (h1 : term382 n) : term382 n.
Proof. exact (h1). Qed.
Lemma lem2540303 (n : int) (h1 : term382 n) : term322.
Proof. exact (proj2 (@lem2540302 n h1)). Qed.
Lemma lem2540306 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2540307 : term322 = term383.
Proof. exact (@lem2540306 term166 term243). Qed.
Lemma lem2540309 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540310 : term243 = term248.
Proof. exact (@lem2540309 term160). Qed.
Lemma lem2540312 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540313 : term166 = term315.
Proof. exact (@lem2540312 (NUMERAL 0)). Qed.
Lemma lem2540314 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540315 : term384 = term385.
Proof. exact (MK_COMB (@lem2540314) (@lem2540313)). Qed.
Lemma lem2540316 : term383 = term386.
Proof. exact (MK_COMB (@lem2540315) (@lem2540310)). Qed.
Lemma lem2540317 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2540319 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540320 : term300 = term301.
Proof. exact (@lem2540319 (NUMERAL 0) term160). Qed.
Lemma lem2540321 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540322 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540323 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540322 h1) (fun h1 : term301 = True => @lem2540321)). Qed.
Lemma lem2540324 : term301 = True.
Proof. exact (EQ_MP (@lem2540323) (@lem2540321)). Qed.
Lemma lem2540325 : term300 = True.
Proof. exact (TRANS (@lem2540320) (@lem2540324)). Qed.
Lemma lem2540326 : True = term300.
Proof. exact (SYM (@lem2540325)). Qed.
Lemma lem2540327 : term300.
Proof. exact (EQ_MP (@lem2540326) (@lem0)). Qed.
Lemma lem2540328 : term388.
Proof. exact (@lem2540317 (@lem2540327)). Qed.
Lemma lem2540330 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540331 : term300 = term301.
Proof. exact (@lem2540330 (NUMERAL 0) term160). Qed.
Lemma lem2540332 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540333 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540334 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540333 h1) (fun h1 : term301 = True => @lem2540332)). Qed.
Lemma lem2540335 : term301 = True.
Proof. exact (EQ_MP (@lem2540334) (@lem2540332)). Qed.
Lemma lem2540336 : term300 = True.
Proof. exact (TRANS (@lem2540331) (@lem2540335)). Qed.
Lemma lem2540337 : True = term300.
Proof. exact (SYM (@lem2540336)). Qed.
Lemma lem2540338 : term300.
Proof. exact (EQ_MP (@lem2540337) (@lem0)). Qed.
Lemma lem2540339 : term386 = term389.
Proof. exact (@lem2540328 (@lem2540338)). Qed.
Lemma lem2540341 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540342 : term251 = term262.
Proof. exact (@lem2540341 term160 term160). Qed.
Lemma lem2540343 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540344 : term259 = term160.
Proof. exact (EQ_MP (@lem2540343) (@lem940073)). Qed.
Lemma lem2540345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540346 : term257 = term159.
Proof. exact (MK_COMB (@lem2540345) (@lem2540344)). Qed.
Lemma lem2540347 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540348 : term262 = term243.
Proof. exact (MK_COMB (@lem2540347) (@lem2540346)). Qed.
Lemma lem2540349 : term251 = term243.
Proof. exact (TRANS (@lem2540342) (@lem2540348)). Qed.
Lemma lem2540351 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540352 : term312 = term166.
Proof. exact (@lem2540351 term160). Qed.
Lemma lem2540353 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540354 : term390 = term384.
Proof. exact (MK_COMB (@lem2540353) (@lem2540352)). Qed.
Lemma lem2540355 : term389 = term383.
Proof. exact (MK_COMB (@lem2540354) (@lem2540349)). Qed.
Lemma lem2540357 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2540358 : term383 = term393.
Proof. exact (@lem2540357 (NUMERAL 0) term160). Qed.
Lemma lem2540359 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540360 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2540361 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540360 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2540359)). Qed.
Lemma lem2540362 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2540361) (@lem2540359)). Qed.
Lemma lem2540363 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2540364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2540365 : term394 = (and True).
Proof. exact (MK_COMB (@lem2540364) (@lem2540363)). Qed.
Lemma lem2540366 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2540365) (@lem2540362)). Qed.
Lemma lem2540368 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2540369 : term393 = False.
Proof. exact (TRANS (@lem2540366) (@lem2540368)). Qed.
Lemma lem2540370 : term383 = False.
Proof. exact (TRANS (@lem2540358) (@lem2540369)). Qed.
Lemma lem2540371 : term389 = False.
Proof. exact (TRANS (@lem2540355) (@lem2540370)). Qed.
Lemma lem2540372 : term386 = False.
Proof. exact (TRANS (@lem2540339) (@lem2540371)). Qed.
Lemma lem2540373 : term383 = False.
Proof. exact (TRANS (@lem2540316) (@lem2540372)). Qed.
Lemma lem2540374 : term322 = False.
Proof. exact (TRANS (@lem2540307) (@lem2540373)). Qed.
Lemma lem2540375 (n : int) (h1 : term382 n) : False.
Proof. exact (EQ_MP (@lem2540374) (@lem2540303 n h1)). Qed.
Lemma lem2540376 (n : int) (h1 : term395 n) : term395 n.
Proof. exact (h1). Qed.
Lemma lem2540377 (n : int) (h1 : term395 n) : term322.
Proof. exact (proj2 (@lem2540376 n h1)). Qed.
Lemma lem2540380 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2540381 : term322 = term383.
Proof. exact (@lem2540380 term166 term243). Qed.
Lemma lem2540383 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540384 : term243 = term248.
Proof. exact (@lem2540383 term160). Qed.
Lemma lem2540386 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540387 : term166 = term315.
Proof. exact (@lem2540386 (NUMERAL 0)). Qed.
Lemma lem2540388 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540389 : term384 = term385.
Proof. exact (MK_COMB (@lem2540388) (@lem2540387)). Qed.
Lemma lem2540390 : term383 = term386.
Proof. exact (MK_COMB (@lem2540389) (@lem2540384)). Qed.
Lemma lem2540391 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2540393 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540394 : term300 = term301.
Proof. exact (@lem2540393 (NUMERAL 0) term160). Qed.
Lemma lem2540395 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540396 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540397 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540396 h1) (fun h1 : term301 = True => @lem2540395)). Qed.
Lemma lem2540398 : term301 = True.
Proof. exact (EQ_MP (@lem2540397) (@lem2540395)). Qed.
Lemma lem2540399 : term300 = True.
Proof. exact (TRANS (@lem2540394) (@lem2540398)). Qed.
Lemma lem2540400 : True = term300.
Proof. exact (SYM (@lem2540399)). Qed.
Lemma lem2540401 : term300.
Proof. exact (EQ_MP (@lem2540400) (@lem0)). Qed.
Lemma lem2540402 : term388.
Proof. exact (@lem2540391 (@lem2540401)). Qed.
Lemma lem2540404 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540405 : term300 = term301.
Proof. exact (@lem2540404 (NUMERAL 0) term160). Qed.
Lemma lem2540406 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540407 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540408 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540407 h1) (fun h1 : term301 = True => @lem2540406)). Qed.
Lemma lem2540409 : term301 = True.
Proof. exact (EQ_MP (@lem2540408) (@lem2540406)). Qed.
Lemma lem2540410 : term300 = True.
Proof. exact (TRANS (@lem2540405) (@lem2540409)). Qed.
Lemma lem2540411 : True = term300.
Proof. exact (SYM (@lem2540410)). Qed.
Lemma lem2540412 : term300.
Proof. exact (EQ_MP (@lem2540411) (@lem0)). Qed.
Lemma lem2540413 : term386 = term389.
Proof. exact (@lem2540402 (@lem2540412)). Qed.
Lemma lem2540415 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540416 : term251 = term262.
Proof. exact (@lem2540415 term160 term160). Qed.
Lemma lem2540417 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540418 : term259 = term160.
Proof. exact (EQ_MP (@lem2540417) (@lem940073)). Qed.
Lemma lem2540419 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540420 : term257 = term159.
Proof. exact (MK_COMB (@lem2540419) (@lem2540418)). Qed.
Lemma lem2540421 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540422 : term262 = term243.
Proof. exact (MK_COMB (@lem2540421) (@lem2540420)). Qed.
Lemma lem2540423 : term251 = term243.
Proof. exact (TRANS (@lem2540416) (@lem2540422)). Qed.
Lemma lem2540425 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540426 : term312 = term166.
Proof. exact (@lem2540425 term160). Qed.
Lemma lem2540427 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540428 : term390 = term384.
Proof. exact (MK_COMB (@lem2540427) (@lem2540426)). Qed.
Lemma lem2540429 : term389 = term383.
Proof. exact (MK_COMB (@lem2540428) (@lem2540423)). Qed.
Lemma lem2540431 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2540432 : term383 = term393.
Proof. exact (@lem2540431 (NUMERAL 0) term160). Qed.
Lemma lem2540433 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540434 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2540435 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540434 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2540433)). Qed.
Lemma lem2540436 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2540435) (@lem2540433)). Qed.
Lemma lem2540437 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2540438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2540439 : term394 = (and True).
Proof. exact (MK_COMB (@lem2540438) (@lem2540437)). Qed.
Lemma lem2540440 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2540439) (@lem2540436)). Qed.
Lemma lem2540442 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2540443 : term393 = False.
Proof. exact (TRANS (@lem2540440) (@lem2540442)). Qed.
Lemma lem2540444 : term383 = False.
Proof. exact (TRANS (@lem2540432) (@lem2540443)). Qed.
Lemma lem2540445 : term389 = False.
Proof. exact (TRANS (@lem2540429) (@lem2540444)). Qed.
Lemma lem2540446 : term386 = False.
Proof. exact (TRANS (@lem2540413) (@lem2540445)). Qed.
Lemma lem2540447 : term383 = False.
Proof. exact (TRANS (@lem2540390) (@lem2540446)). Qed.
Lemma lem2540448 : term322 = False.
Proof. exact (TRANS (@lem2540381) (@lem2540447)). Qed.
Lemma lem2540449 (n : int) (h1 : term395 n) : False.
Proof. exact (EQ_MP (@lem2540448) (@lem2540377 n h1)). Qed.
Lemma lem2540450 (n : int) (h1 : term352 n) : False.
Proof. exact (or_elim (@lem2540301 n h1) (fun h0 : term382 n => @lem2540375 n h0) (fun h0 : term395 n => @lem2540449 n h0)). Qed.
Lemma lem2540451 (n : int) (h1 : term379 n) : term379 n.
Proof. exact (h1). Qed.
Lemma lem2540452 (n : int) (h1 : term373 n) : term373 n.
Proof. exact (h1). Qed.
Lemma lem2540453 (n : int) (h1 : term373 n) : term370 n.
Proof. exact (proj2 (@lem2540452 n h1)). Qed.
Lemma lem2540454 (n : int) (h1 : term373 n) : term271 n.
Proof. exact (proj1 (@lem2540452 n h1)). Qed.
Lemma lem2540455 (n : int) (h1 : term373 n) : term368 n.
Proof. exact (proj2 (@lem2540453 n h1)). Qed.
Lemma lem2540458 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2540459 : term396 = term300.
Proof. exact (@lem2540458 term166 term159). Qed.
Lemma lem2540461 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540462 : term159 = term245.
Proof. exact (@lem2540461 term160). Qed.
Lemma lem2540464 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540465 : term166 = term315.
Proof. exact (@lem2540464 (NUMERAL 0)). Qed.
Lemma lem2540466 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540467 : term397 = term398.
Proof. exact (MK_COMB (@lem2540466) (@lem2540465)). Qed.
Lemma lem2540468 : term300 = term399.
Proof. exact (MK_COMB (@lem2540467) (@lem2540462)). Qed.
Lemma lem2540469 : term400.
Proof. exact (@lem1980255 term166 term159 term159 term159). Qed.
Lemma lem2540471 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540472 : term300 = term301.
Proof. exact (@lem2540471 (NUMERAL 0) term160). Qed.
Lemma lem2540473 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540474 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540475 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540474 h1) (fun h1 : term301 = True => @lem2540473)). Qed.
Lemma lem2540476 : term301 = True.
Proof. exact (EQ_MP (@lem2540475) (@lem2540473)). Qed.
Lemma lem2540477 : term300 = True.
Proof. exact (TRANS (@lem2540472) (@lem2540476)). Qed.
Lemma lem2540478 : True = term300.
Proof. exact (SYM (@lem2540477)). Qed.
Lemma lem2540479 : term300.
Proof. exact (EQ_MP (@lem2540478) (@lem0)). Qed.
Lemma lem2540480 : term401.
Proof. exact (@lem2540469 (@lem2540479)). Qed.
Lemma lem2540482 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540483 : term300 = term301.
Proof. exact (@lem2540482 (NUMERAL 0) term160). Qed.
Lemma lem2540484 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540485 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540486 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540485 h1) (fun h1 : term301 = True => @lem2540484)). Qed.
Lemma lem2540487 : term301 = True.
Proof. exact (EQ_MP (@lem2540486) (@lem2540484)). Qed.
Lemma lem2540488 : term300 = True.
Proof. exact (TRANS (@lem2540483) (@lem2540487)). Qed.
Lemma lem2540489 : True = term300.
Proof. exact (SYM (@lem2540488)). Qed.
Lemma lem2540490 : term300.
Proof. exact (EQ_MP (@lem2540489) (@lem0)). Qed.
Lemma lem2540491 : term399 = term402.
Proof. exact (@lem2540480 (@lem2540490)). Qed.
Lemma lem2540493 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2540494 : term256 = term257.
Proof. exact (@lem2540493 term160 term160). Qed.
Lemma lem2540495 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540496 : term259 = term160.
Proof. exact (EQ_MP (@lem2540495) (@lem940073)). Qed.
Lemma lem2540497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540498 : term257 = term159.
Proof. exact (MK_COMB (@lem2540497) (@lem2540496)). Qed.
Lemma lem2540499 : term256 = term159.
Proof. exact (TRANS (@lem2540494) (@lem2540498)). Qed.
Lemma lem2540501 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540502 : term312 = term166.
Proof. exact (@lem2540501 term160). Qed.
Lemma lem2540503 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540504 : term403 = term397.
Proof. exact (MK_COMB (@lem2540503) (@lem2540502)). Qed.
Lemma lem2540505 : term402 = term300.
Proof. exact (MK_COMB (@lem2540504) (@lem2540499)). Qed.
Lemma lem2540507 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540508 : term300 = term301.
Proof. exact (@lem2540507 (NUMERAL 0) term160). Qed.
Lemma lem2540509 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540510 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540511 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540510 h1) (fun h1 : term301 = True => @lem2540509)). Qed.
Lemma lem2540512 : term301 = True.
Proof. exact (EQ_MP (@lem2540511) (@lem2540509)). Qed.
Lemma lem2540513 : term300 = True.
Proof. exact (TRANS (@lem2540508) (@lem2540512)). Qed.
Lemma lem2540514 : term402 = True.
Proof. exact (TRANS (@lem2540505) (@lem2540513)). Qed.
Lemma lem2540515 : term399 = True.
Proof. exact (TRANS (@lem2540491) (@lem2540514)). Qed.
Lemma lem2540516 : term300 = True.
Proof. exact (TRANS (@lem2540468) (@lem2540515)). Qed.
Lemma lem2540517 : term396 = True.
Proof. exact (TRANS (@lem2540459) (@lem2540516)). Qed.
Lemma lem2540518 : True = term396.
Proof. exact (SYM (@lem2540517)). Qed.
Lemma lem2540519 : term396.
Proof. exact (EQ_MP (@lem2540518) (@lem0)). Qed.
Lemma lem2540520 (n : int) (h1 : term373 n) : term404 n.
Proof. exact (conj (@lem2540519) (@lem2540455 n h1)). Qed.
Lemma lem2540522 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2540523 (n : int) : term406 n.
Proof. exact (@lem2540522 term159 (real_of_int n)). Qed.
Lemma lem2540524 (n : int) (h1 : term373 n) : term367 n.
Proof. exact (@lem2540523 n (@lem2540520 n h1)). Qed.
Lemma lem2540525 (n : int) : (term195 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2540526 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2540527 (n : int) : (term365 n) = (term366 n).
Proof. exact (MK_COMB (@lem2540526) (@lem2540525 n)). Qed.
Lemma lem2540528 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2540529 (n : int) : (term367 n) = (term368 n).
Proof. exact (MK_COMB (@lem2540527 n) (@lem2540528)). Qed.
Lemma lem2540530 (n : int) (h1 : term373 n) : term368 n.
Proof. exact (EQ_MP (@lem2540529 n) (@lem2540524 n h1)). Qed.
Lemma lem2540532 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2540533 : term396 = term300.
Proof. exact (@lem2540532 term166 term159). Qed.
Lemma lem2540535 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540536 : term159 = term245.
Proof. exact (@lem2540535 term160). Qed.
Lemma lem2540538 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540539 : term166 = term315.
Proof. exact (@lem2540538 (NUMERAL 0)). Qed.
Lemma lem2540540 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540541 : term397 = term398.
Proof. exact (MK_COMB (@lem2540540) (@lem2540539)). Qed.
Lemma lem2540542 : term300 = term399.
Proof. exact (MK_COMB (@lem2540541) (@lem2540536)). Qed.
Lemma lem2540543 : term400.
Proof. exact (@lem1980255 term166 term159 term159 term159). Qed.
Lemma lem2540545 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540546 : term300 = term301.
Proof. exact (@lem2540545 (NUMERAL 0) term160). Qed.
Lemma lem2540547 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540548 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540549 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540548 h1) (fun h1 : term301 = True => @lem2540547)). Qed.
Lemma lem2540550 : term301 = True.
Proof. exact (EQ_MP (@lem2540549) (@lem2540547)). Qed.
Lemma lem2540551 : term300 = True.
Proof. exact (TRANS (@lem2540546) (@lem2540550)). Qed.
Lemma lem2540552 : True = term300.
Proof. exact (SYM (@lem2540551)). Qed.
Lemma lem2540553 : term300.
Proof. exact (EQ_MP (@lem2540552) (@lem0)). Qed.
Lemma lem2540554 : term401.
Proof. exact (@lem2540543 (@lem2540553)). Qed.
Lemma lem2540556 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540557 : term300 = term301.
Proof. exact (@lem2540556 (NUMERAL 0) term160). Qed.
Lemma lem2540558 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540559 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540560 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540559 h1) (fun h1 : term301 = True => @lem2540558)). Qed.
Lemma lem2540561 : term301 = True.
Proof. exact (EQ_MP (@lem2540560) (@lem2540558)). Qed.
Lemma lem2540562 : term300 = True.
Proof. exact (TRANS (@lem2540557) (@lem2540561)). Qed.
Lemma lem2540563 : True = term300.
Proof. exact (SYM (@lem2540562)). Qed.
Lemma lem2540564 : term300.
Proof. exact (EQ_MP (@lem2540563) (@lem0)). Qed.
Lemma lem2540565 : term399 = term402.
Proof. exact (@lem2540554 (@lem2540564)). Qed.
Lemma lem2540567 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2540568 : term256 = term257.
Proof. exact (@lem2540567 term160 term160). Qed.
Lemma lem2540569 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540570 : term259 = term160.
Proof. exact (EQ_MP (@lem2540569) (@lem940073)). Qed.
Lemma lem2540571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540572 : term257 = term159.
Proof. exact (MK_COMB (@lem2540571) (@lem2540570)). Qed.
Lemma lem2540573 : term256 = term159.
Proof. exact (TRANS (@lem2540568) (@lem2540572)). Qed.
Lemma lem2540575 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540576 : term312 = term166.
Proof. exact (@lem2540575 term160). Qed.
Lemma lem2540577 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540578 : term403 = term397.
Proof. exact (MK_COMB (@lem2540577) (@lem2540576)). Qed.
Lemma lem2540579 : term402 = term300.
Proof. exact (MK_COMB (@lem2540578) (@lem2540573)). Qed.
Lemma lem2540581 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540582 : term300 = term301.
Proof. exact (@lem2540581 (NUMERAL 0) term160). Qed.
Lemma lem2540583 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540584 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540585 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540584 h1) (fun h1 : term301 = True => @lem2540583)). Qed.
Lemma lem2540586 : term301 = True.
Proof. exact (EQ_MP (@lem2540585) (@lem2540583)). Qed.
Lemma lem2540587 : term300 = True.
Proof. exact (TRANS (@lem2540582) (@lem2540586)). Qed.
Lemma lem2540588 : term402 = True.
Proof. exact (TRANS (@lem2540579) (@lem2540587)). Qed.
Lemma lem2540589 : term399 = True.
Proof. exact (TRANS (@lem2540565) (@lem2540588)). Qed.
Lemma lem2540590 : term300 = True.
Proof. exact (TRANS (@lem2540542) (@lem2540589)). Qed.
Lemma lem2540591 : term396 = True.
Proof. exact (TRANS (@lem2540533) (@lem2540590)). Qed.
Lemma lem2540592 : True = term396.
Proof. exact (SYM (@lem2540591)). Qed.
Lemma lem2540593 : term396.
Proof. exact (EQ_MP (@lem2540592) (@lem0)). Qed.
Lemma lem2540594 (n : int) (h1 : term373 n) : term407 n.
Proof. exact (conj (@lem2540593) (@lem2540454 n h1)). Qed.
Lemma lem2540596 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2540597 (n : int) : term408 n.
Proof. exact (@lem2540596 term159 (term267 n)). Qed.
Lemma lem2540598 (n : int) (h1 : term373 n) : term409 n.
Proof. exact (@lem2540597 n (@lem2540594 n h1)). Qed.
Lemma lem2540599 (n : int) : (term410 n) = (term267 n).
Proof. exact (@lem1982733 (term267 n)). Qed.
Lemma lem2540600 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2540601 (n : int) : (term411 n) = (term270 n).
Proof. exact (MK_COMB (@lem2540600) (@lem2540599 n)). Qed.
Lemma lem2540602 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2540603 (n : int) : (term409 n) = (term271 n).
Proof. exact (MK_COMB (@lem2540601 n) (@lem2540602)). Qed.
Lemma lem2540604 (n : int) (h1 : term373 n) : term271 n.
Proof. exact (EQ_MP (@lem2540603 n) (@lem2540598 n h1)). Qed.
Lemma lem2540605 (n : int) (h1 : term373 n) : term412 n.
Proof. exact (conj (@lem2540604 n h1) (@lem2540530 n h1)). Qed.
Lemma lem2540607 (x : real) (y : real) : term413 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2540608 (n : int) : term414 n.
Proof. exact (@lem2540607 (term267 n) (real_of_int n)). Qed.
Lemma lem2540609 (n : int) (h1 : term373 n) : term415 n.
Proof. exact (@lem2540608 n (@lem2540605 n h1)). Qed.
Lemma lem2540610 (n : int) : (term416 n) = (term417 n).
Proof. exact (@lem1982759 (term291 n) (real_of_int n) term243). Qed.
Lemma lem2540611 (n : int) : (term418 n) = (term293 n).
Proof. exact (@lem1982713 term243 (real_of_int n)). Qed.
Lemma lem2540613 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540614 : term159 = term245.
Proof. exact (@lem2540613 term160). Qed.
Lemma lem2540616 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540617 : term243 = term248.
Proof. exact (@lem2540616 term160). Qed.
Lemma lem2540618 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2540619 : term294 = term295.
Proof. exact (MK_COMB (@lem2540618) (@lem2540617)). Qed.
Lemma lem2540620 : term296 = term297.
Proof. exact (MK_COMB (@lem2540619) (@lem2540614)). Qed.
Lemma lem2540621 : term298.
Proof. exact (@lem1981473 term243 term159 term159 term159 term166 term159). Qed.
Lemma lem2540623 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540624 : term300 = term301.
Proof. exact (@lem2540623 (NUMERAL 0) term160). Qed.
Lemma lem2540625 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540626 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540627 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540626 h1) (fun h1 : term301 = True => @lem2540625)). Qed.
Lemma lem2540628 : term301 = True.
Proof. exact (EQ_MP (@lem2540627) (@lem2540625)). Qed.
Lemma lem2540629 : term300 = True.
Proof. exact (TRANS (@lem2540624) (@lem2540628)). Qed.
Lemma lem2540630 : True = term300.
Proof. exact (SYM (@lem2540629)). Qed.
Lemma lem2540631 : term300.
Proof. exact (EQ_MP (@lem2540630) (@lem0)). Qed.
Lemma lem2540632 : term303.
Proof. exact (@lem2540621 (@lem2540631)). Qed.
Lemma lem2540634 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540635 : term300 = term301.
Proof. exact (@lem2540634 (NUMERAL 0) term160). Qed.
Lemma lem2540636 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540637 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540638 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540637 h1) (fun h1 : term301 = True => @lem2540636)). Qed.
Lemma lem2540639 : term301 = True.
Proof. exact (EQ_MP (@lem2540638) (@lem2540636)). Qed.
Lemma lem2540640 : term300 = True.
Proof. exact (TRANS (@lem2540635) (@lem2540639)). Qed.
Lemma lem2540641 : True = term300.
Proof. exact (SYM (@lem2540640)). Qed.
Lemma lem2540642 : term300.
Proof. exact (EQ_MP (@lem2540641) (@lem0)). Qed.
Lemma lem2540643 : term304.
Proof. exact (@lem2540632 (@lem2540642)). Qed.
Lemma lem2540645 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540646 : term300 = term301.
Proof. exact (@lem2540645 (NUMERAL 0) term160). Qed.
Lemma lem2540647 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540648 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540649 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540648 h1) (fun h1 : term301 = True => @lem2540647)). Qed.
Lemma lem2540650 : term301 = True.
Proof. exact (EQ_MP (@lem2540649) (@lem2540647)). Qed.
Lemma lem2540651 : term300 = True.
Proof. exact (TRANS (@lem2540646) (@lem2540650)). Qed.
Lemma lem2540652 : True = term300.
Proof. exact (SYM (@lem2540651)). Qed.
Lemma lem2540653 : term300.
Proof. exact (EQ_MP (@lem2540652) (@lem0)). Qed.
Lemma lem2540654 : term305.
Proof. exact (@lem2540643 (@lem2540653)). Qed.
Lemma lem2540656 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2540657 : term256 = term257.
Proof. exact (@lem2540656 term160 term160). Qed.
Lemma lem2540658 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540659 : term259 = term160.
Proof. exact (EQ_MP (@lem2540658) (@lem940073)). Qed.
Lemma lem2540660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540661 : term257 = term159.
Proof. exact (MK_COMB (@lem2540660) (@lem2540659)). Qed.
Lemma lem2540662 : term256 = term159.
Proof. exact (TRANS (@lem2540657) (@lem2540661)). Qed.
Lemma lem2540664 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540665 : term251 = term262.
Proof. exact (@lem2540664 term160 term160). Qed.
Lemma lem2540666 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540667 : term259 = term160.
Proof. exact (EQ_MP (@lem2540666) (@lem940073)). Qed.
Lemma lem2540668 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540669 : term257 = term159.
Proof. exact (MK_COMB (@lem2540668) (@lem2540667)). Qed.
Lemma lem2540670 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540671 : term262 = term243.
Proof. exact (MK_COMB (@lem2540670) (@lem2540669)). Qed.
Lemma lem2540672 : term251 = term243.
Proof. exact (TRANS (@lem2540665) (@lem2540671)). Qed.
Lemma lem2540673 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2540674 : term306 = term294.
Proof. exact (MK_COMB (@lem2540673) (@lem2540672)). Qed.
Lemma lem2540675 : term307 = term296.
Proof. exact (MK_COMB (@lem2540674) (@lem2540662)). Qed.
Lemma lem2540677 (m : nat) : (term308 m) = term166.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2540678 : term296 = term166.
Proof. exact (@lem2540677 term160). Qed.
Lemma lem2540679 : term307 = term166.
Proof. exact (TRANS (@lem2540675) (@lem2540678)). Qed.
Lemma lem2540680 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2540681 : term309 = term310.
Proof. exact (MK_COMB (@lem2540680) (@lem2540679)). Qed.
Lemma lem2540682 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2540683 : term311 = term312.
Proof. exact (MK_COMB (@lem2540681) (@lem2540682)). Qed.
Lemma lem2540685 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540686 : term312 = term166.
Proof. exact (@lem2540685 term160). Qed.
Lemma lem2540687 : term311 = term166.
Proof. exact (TRANS (@lem2540683) (@lem2540686)). Qed.
Lemma lem2540689 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2540690 : term256 = term257.
Proof. exact (@lem2540689 term160 term160). Qed.
Lemma lem2540691 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540692 : term259 = term160.
Proof. exact (EQ_MP (@lem2540691) (@lem940073)). Qed.
Lemma lem2540693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540694 : term257 = term159.
Proof. exact (MK_COMB (@lem2540693) (@lem2540692)). Qed.
Lemma lem2540695 : term256 = term159.
Proof. exact (TRANS (@lem2540690) (@lem2540694)). Qed.
Lemma lem2540696 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem2540697 : term314 = term312.
Proof. exact (MK_COMB (@lem2540696) (@lem2540695)). Qed.
Lemma lem2540699 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540700 : term312 = term166.
Proof. exact (@lem2540699 term160). Qed.
Lemma lem2540701 : term314 = term166.
Proof. exact (TRANS (@lem2540697) (@lem2540700)). Qed.
Lemma lem2540702 : term166 = term314.
Proof. exact (SYM (@lem2540701)). Qed.
Lemma lem2540703 : term311 = term314.
Proof. exact (TRANS (@lem2540687) (@lem2540702)). Qed.
Lemma lem2540704 : term297 = term315.
Proof. exact (@lem2540654 (@lem2540703)). Qed.
Lemma lem2540705 : term296 = term315.
Proof. exact (TRANS (@lem2540620) (@lem2540704)). Qed.
Lemma lem2540707 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2540708 : term315 = term166.
Proof. exact (@lem2540707 term166). Qed.
Lemma lem2540709 : term296 = term166.
Proof. exact (TRANS (@lem2540705) (@lem2540708)). Qed.
Lemma lem2540710 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2540711 : term316 = term310.
Proof. exact (MK_COMB (@lem2540710) (@lem2540709)). Qed.
Lemma lem2540712 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2540713 (n : int) : (term293 n) = (term317 n).
Proof. exact (MK_COMB (@lem2540711) (@lem2540712 n)). Qed.
Lemma lem2540714 (n : int) : (term418 n) = (term317 n).
Proof. exact (TRANS (@lem2540611 n) (@lem2540713 n)). Qed.
Lemma lem2540715 (n : int) : (term317 n) = term166.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2540716 (n : int) : (term418 n) = term166.
Proof. exact (TRANS (@lem2540714 n) (@lem2540715 n)). Qed.
Lemma lem2540717 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2540718 (n : int) : (term419 n) = term176.
Proof. exact (MK_COMB (@lem2540717) (@lem2540716 n)). Qed.
Lemma lem2540719 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem2540720 (n : int) : (term417 n) = term319.
Proof. exact (MK_COMB (@lem2540718 n) (@lem2540719)). Qed.
Lemma lem2540721 (n : int) : (term416 n) = term319.
Proof. exact (TRANS (@lem2540610 n) (@lem2540720 n)). Qed.
Lemma lem2540722 : term319 = term243.
Proof. exact (@lem1982721 term243). Qed.
Lemma lem2540723 (n : int) : (term416 n) = term243.
Proof. exact (TRANS (@lem2540721 n) (@lem2540722)). Qed.
Lemma lem2540724 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2540725 (n : int) : (term420 n) = term321.
Proof. exact (MK_COMB (@lem2540724) (@lem2540723 n)). Qed.
Lemma lem2540726 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2540727 (n : int) : (term415 n) = term322.
Proof. exact (MK_COMB (@lem2540725 n) (@lem2540726)). Qed.
Lemma lem2540728 (n : int) (h1 : term373 n) : term322.
Proof. exact (EQ_MP (@lem2540727 n) (@lem2540609 n h1)). Qed.
Lemma lem2540730 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2540731 : term322 = term383.
Proof. exact (@lem2540730 term166 term243). Qed.
Lemma lem2540733 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540734 : term243 = term248.
Proof. exact (@lem2540733 term160). Qed.
Lemma lem2540736 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540737 : term166 = term315.
Proof. exact (@lem2540736 (NUMERAL 0)). Qed.
Lemma lem2540738 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540739 : term384 = term385.
Proof. exact (MK_COMB (@lem2540738) (@lem2540737)). Qed.
Lemma lem2540740 : term383 = term386.
Proof. exact (MK_COMB (@lem2540739) (@lem2540734)). Qed.
Lemma lem2540741 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2540743 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540744 : term300 = term301.
Proof. exact (@lem2540743 (NUMERAL 0) term160). Qed.
Lemma lem2540745 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540746 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540747 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540746 h1) (fun h1 : term301 = True => @lem2540745)). Qed.
Lemma lem2540748 : term301 = True.
Proof. exact (EQ_MP (@lem2540747) (@lem2540745)). Qed.
Lemma lem2540749 : term300 = True.
Proof. exact (TRANS (@lem2540744) (@lem2540748)). Qed.
Lemma lem2540750 : True = term300.
Proof. exact (SYM (@lem2540749)). Qed.
Lemma lem2540751 : term300.
Proof. exact (EQ_MP (@lem2540750) (@lem0)). Qed.
Lemma lem2540752 : term388.
Proof. exact (@lem2540741 (@lem2540751)). Qed.
Lemma lem2540754 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540755 : term300 = term301.
Proof. exact (@lem2540754 (NUMERAL 0) term160). Qed.
Lemma lem2540756 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540757 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540758 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540757 h1) (fun h1 : term301 = True => @lem2540756)). Qed.
Lemma lem2540759 : term301 = True.
Proof. exact (EQ_MP (@lem2540758) (@lem2540756)). Qed.
Lemma lem2540760 : term300 = True.
Proof. exact (TRANS (@lem2540755) (@lem2540759)). Qed.
Lemma lem2540761 : True = term300.
Proof. exact (SYM (@lem2540760)). Qed.
Lemma lem2540762 : term300.
Proof. exact (EQ_MP (@lem2540761) (@lem0)). Qed.
Lemma lem2540763 : term386 = term389.
Proof. exact (@lem2540752 (@lem2540762)). Qed.
Lemma lem2540765 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2540766 : term251 = term262.
Proof. exact (@lem2540765 term160 term160). Qed.
Lemma lem2540767 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540768 : term259 = term160.
Proof. exact (EQ_MP (@lem2540767) (@lem940073)). Qed.
Lemma lem2540769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540770 : term257 = term159.
Proof. exact (MK_COMB (@lem2540769) (@lem2540768)). Qed.
Lemma lem2540771 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2540772 : term262 = term243.
Proof. exact (MK_COMB (@lem2540771) (@lem2540770)). Qed.
Lemma lem2540773 : term251 = term243.
Proof. exact (TRANS (@lem2540766) (@lem2540772)). Qed.
Lemma lem2540775 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540776 : term312 = term166.
Proof. exact (@lem2540775 term160). Qed.
Lemma lem2540777 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2540778 : term390 = term384.
Proof. exact (MK_COMB (@lem2540777) (@lem2540776)). Qed.
Lemma lem2540779 : term389 = term383.
Proof. exact (MK_COMB (@lem2540778) (@lem2540773)). Qed.
Lemma lem2540781 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2540782 : term383 = term393.
Proof. exact (@lem2540781 (NUMERAL 0) term160). Qed.
Lemma lem2540783 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540784 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2540785 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540784 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2540783)). Qed.
Lemma lem2540786 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2540785) (@lem2540783)). Qed.
Lemma lem2540787 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2540788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2540789 : term394 = (and True).
Proof. exact (MK_COMB (@lem2540788) (@lem2540787)). Qed.
Lemma lem2540790 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2540789) (@lem2540786)). Qed.
Lemma lem2540792 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2540793 : term393 = False.
Proof. exact (TRANS (@lem2540790) (@lem2540792)). Qed.
Lemma lem2540794 : term383 = False.
Proof. exact (TRANS (@lem2540782) (@lem2540793)). Qed.
Lemma lem2540795 : term389 = False.
Proof. exact (TRANS (@lem2540779) (@lem2540794)). Qed.
Lemma lem2540796 : term386 = False.
Proof. exact (TRANS (@lem2540763) (@lem2540795)). Qed.
Lemma lem2540797 : term383 = False.
Proof. exact (TRANS (@lem2540740) (@lem2540796)). Qed.
Lemma lem2540798 : term322 = False.
Proof. exact (TRANS (@lem2540731) (@lem2540797)). Qed.
Lemma lem2540799 (n : int) (h1 : term373 n) : False.
Proof. exact (EQ_MP (@lem2540798) (@lem2540728 n h1)). Qed.
Lemma lem2540800 (n : int) (h1 : term376 n) : term376 n.
Proof. exact (h1). Qed.
Lemma lem2540801 (n : int) (h1 : term376 n) : term370 n.
Proof. exact (proj2 (@lem2540800 n h1)). Qed.
Lemma lem2540802 (n : int) (h1 : term376 n) : term280 n.
Proof. exact (proj1 (@lem2540800 n h1)). Qed.
Lemma lem2540804 (n : int) (h1 : term376 n) : term421 n.
Proof. exact (proj1 (@lem2540801 n h1)). Qed.
Lemma lem2540806 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2540807 : term396 = term300.
Proof. exact (@lem2540806 term166 term159). Qed.
Lemma lem2540809 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540810 : term159 = term245.
Proof. exact (@lem2540809 term160). Qed.
Lemma lem2540812 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540813 : term166 = term315.
Proof. exact (@lem2540812 (NUMERAL 0)). Qed.
Lemma lem2540814 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540815 : term397 = term398.
Proof. exact (MK_COMB (@lem2540814) (@lem2540813)). Qed.
Lemma lem2540816 : term300 = term399.
Proof. exact (MK_COMB (@lem2540815) (@lem2540810)). Qed.
Lemma lem2540817 : term400.
Proof. exact (@lem1980255 term166 term159 term159 term159). Qed.
Lemma lem2540819 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540820 : term300 = term301.
Proof. exact (@lem2540819 (NUMERAL 0) term160). Qed.
Lemma lem2540821 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540822 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540823 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540822 h1) (fun h1 : term301 = True => @lem2540821)). Qed.
Lemma lem2540824 : term301 = True.
Proof. exact (EQ_MP (@lem2540823) (@lem2540821)). Qed.
Lemma lem2540825 : term300 = True.
Proof. exact (TRANS (@lem2540820) (@lem2540824)). Qed.
Lemma lem2540826 : True = term300.
Proof. exact (SYM (@lem2540825)). Qed.
Lemma lem2540827 : term300.
Proof. exact (EQ_MP (@lem2540826) (@lem0)). Qed.
Lemma lem2540828 : term401.
Proof. exact (@lem2540817 (@lem2540827)). Qed.
Lemma lem2540830 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540831 : term300 = term301.
Proof. exact (@lem2540830 (NUMERAL 0) term160). Qed.
Lemma lem2540832 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540833 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540834 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540833 h1) (fun h1 : term301 = True => @lem2540832)). Qed.
Lemma lem2540835 : term301 = True.
Proof. exact (EQ_MP (@lem2540834) (@lem2540832)). Qed.
Lemma lem2540836 : term300 = True.
Proof. exact (TRANS (@lem2540831) (@lem2540835)). Qed.
Lemma lem2540837 : True = term300.
Proof. exact (SYM (@lem2540836)). Qed.
Lemma lem2540838 : term300.
Proof. exact (EQ_MP (@lem2540837) (@lem0)). Qed.
Lemma lem2540839 : term399 = term402.
Proof. exact (@lem2540828 (@lem2540838)). Qed.
Lemma lem2540841 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2540842 : term256 = term257.
Proof. exact (@lem2540841 term160 term160). Qed.
Lemma lem2540843 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540844 : term259 = term160.
Proof. exact (EQ_MP (@lem2540843) (@lem940073)). Qed.
Lemma lem2540845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540846 : term257 = term159.
Proof. exact (MK_COMB (@lem2540845) (@lem2540844)). Qed.
Lemma lem2540847 : term256 = term159.
Proof. exact (TRANS (@lem2540842) (@lem2540846)). Qed.
Lemma lem2540849 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540850 : term312 = term166.
Proof. exact (@lem2540849 term160). Qed.
Lemma lem2540851 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540852 : term403 = term397.
Proof. exact (MK_COMB (@lem2540851) (@lem2540850)). Qed.
Lemma lem2540853 : term402 = term300.
Proof. exact (MK_COMB (@lem2540852) (@lem2540847)). Qed.
Lemma lem2540855 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540856 : term300 = term301.
Proof. exact (@lem2540855 (NUMERAL 0) term160). Qed.
Lemma lem2540857 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540858 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540859 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540858 h1) (fun h1 : term301 = True => @lem2540857)). Qed.
Lemma lem2540860 : term301 = True.
Proof. exact (EQ_MP (@lem2540859) (@lem2540857)). Qed.
Lemma lem2540861 : term300 = True.
Proof. exact (TRANS (@lem2540856) (@lem2540860)). Qed.
Lemma lem2540862 : term402 = True.
Proof. exact (TRANS (@lem2540853) (@lem2540861)). Qed.
Lemma lem2540863 : term399 = True.
Proof. exact (TRANS (@lem2540839) (@lem2540862)). Qed.
Lemma lem2540864 : term300 = True.
Proof. exact (TRANS (@lem2540816) (@lem2540863)). Qed.
Lemma lem2540865 : term396 = True.
Proof. exact (TRANS (@lem2540807) (@lem2540864)). Qed.
Lemma lem2540866 : True = term396.
Proof. exact (SYM (@lem2540865)). Qed.
Lemma lem2540867 : term396.
Proof. exact (EQ_MP (@lem2540866) (@lem0)). Qed.
Lemma lem2540868 (n : int) (h1 : term376 n) : term422 n.
Proof. exact (conj (@lem2540867) (@lem2540802 n h1)). Qed.
Lemma lem2540870 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2540871 (n : int) : term423 n.
Proof. exact (@lem2540870 term159 (term277 n)). Qed.
Lemma lem2540872 (n : int) (h1 : term376 n) : term424 n.
Proof. exact (@lem2540871 n (@lem2540868 n h1)). Qed.
Lemma lem2540873 (n : int) : (term425 n) = (term277 n).
Proof. exact (@lem1982733 (term277 n)). Qed.
Lemma lem2540874 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2540875 (n : int) : (term426 n) = (term279 n).
Proof. exact (MK_COMB (@lem2540874) (@lem2540873 n)). Qed.
Lemma lem2540876 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2540877 (n : int) : (term424 n) = (term280 n).
Proof. exact (MK_COMB (@lem2540875 n) (@lem2540876)). Qed.
Lemma lem2540878 (n : int) (h1 : term376 n) : term280 n.
Proof. exact (EQ_MP (@lem2540877 n) (@lem2540872 n h1)). Qed.
Lemma lem2540880 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2540881 : term396 = term300.
Proof. exact (@lem2540880 term166 term159). Qed.
Lemma lem2540883 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540884 : term159 = term245.
Proof. exact (@lem2540883 term160). Qed.
Lemma lem2540886 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540887 : term166 = term315.
Proof. exact (@lem2540886 (NUMERAL 0)). Qed.
Lemma lem2540888 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540889 : term397 = term398.
Proof. exact (MK_COMB (@lem2540888) (@lem2540887)). Qed.
Lemma lem2540890 : term300 = term399.
Proof. exact (MK_COMB (@lem2540889) (@lem2540884)). Qed.
Lemma lem2540891 : term400.
Proof. exact (@lem1980255 term166 term159 term159 term159). Qed.
Lemma lem2540893 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540894 : term300 = term301.
Proof. exact (@lem2540893 (NUMERAL 0) term160). Qed.
Lemma lem2540895 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540896 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540897 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540896 h1) (fun h1 : term301 = True => @lem2540895)). Qed.
Lemma lem2540898 : term301 = True.
Proof. exact (EQ_MP (@lem2540897) (@lem2540895)). Qed.
Lemma lem2540899 : term300 = True.
Proof. exact (TRANS (@lem2540894) (@lem2540898)). Qed.
Lemma lem2540900 : True = term300.
Proof. exact (SYM (@lem2540899)). Qed.
Lemma lem2540901 : term300.
Proof. exact (EQ_MP (@lem2540900) (@lem0)). Qed.
Lemma lem2540902 : term401.
Proof. exact (@lem2540891 (@lem2540901)). Qed.
Lemma lem2540904 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540905 : term300 = term301.
Proof. exact (@lem2540904 (NUMERAL 0) term160). Qed.
Lemma lem2540906 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540907 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540908 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540907 h1) (fun h1 : term301 = True => @lem2540906)). Qed.
Lemma lem2540909 : term301 = True.
Proof. exact (EQ_MP (@lem2540908) (@lem2540906)). Qed.
Lemma lem2540910 : term300 = True.
Proof. exact (TRANS (@lem2540905) (@lem2540909)). Qed.
Lemma lem2540911 : True = term300.
Proof. exact (SYM (@lem2540910)). Qed.
Lemma lem2540912 : term300.
Proof. exact (EQ_MP (@lem2540911) (@lem0)). Qed.
Lemma lem2540913 : term399 = term402.
Proof. exact (@lem2540902 (@lem2540912)). Qed.
Lemma lem2540915 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2540916 : term256 = term257.
Proof. exact (@lem2540915 term160 term160). Qed.
Lemma lem2540917 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2540918 : term259 = term160.
Proof. exact (EQ_MP (@lem2540917) (@lem940073)). Qed.
Lemma lem2540919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2540920 : term257 = term159.
Proof. exact (MK_COMB (@lem2540919) (@lem2540918)). Qed.
Lemma lem2540921 : term256 = term159.
Proof. exact (TRANS (@lem2540916) (@lem2540920)). Qed.
Lemma lem2540923 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2540924 : term312 = term166.
Proof. exact (@lem2540923 term160). Qed.
Lemma lem2540925 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2540926 : term403 = term397.
Proof. exact (MK_COMB (@lem2540925) (@lem2540924)). Qed.
Lemma lem2540927 : term402 = term300.
Proof. exact (MK_COMB (@lem2540926) (@lem2540921)). Qed.
Lemma lem2540929 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540930 : term300 = term301.
Proof. exact (@lem2540929 (NUMERAL 0) term160). Qed.
Lemma lem2540931 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540932 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540933 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540932 h1) (fun h1 : term301 = True => @lem2540931)). Qed.
Lemma lem2540934 : term301 = True.
Proof. exact (EQ_MP (@lem2540933) (@lem2540931)). Qed.
Lemma lem2540935 : term300 = True.
Proof. exact (TRANS (@lem2540930) (@lem2540934)). Qed.
Lemma lem2540936 : term402 = True.
Proof. exact (TRANS (@lem2540927) (@lem2540935)). Qed.
Lemma lem2540937 : term399 = True.
Proof. exact (TRANS (@lem2540913) (@lem2540936)). Qed.
Lemma lem2540938 : term300 = True.
Proof. exact (TRANS (@lem2540890) (@lem2540937)). Qed.
Lemma lem2540939 : term396 = True.
Proof. exact (TRANS (@lem2540881) (@lem2540938)). Qed.
Lemma lem2540940 : True = term396.
Proof. exact (SYM (@lem2540939)). Qed.
Lemma lem2540941 : term396.
Proof. exact (EQ_MP (@lem2540940) (@lem0)). Qed.
Lemma lem2540942 (n : int) (h1 : term376 n) : term427 n.
Proof. exact (conj (@lem2540941) (@lem2540804 n h1)). Qed.
Lemma lem2540944 (x : real) (y : real) : term405 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2540945 (n : int) : term428 n.
Proof. exact (@lem2540944 term159 (term291 n)). Qed.
Lemma lem2540946 (n : int) (h1 : term376 n) : term429 n.
Proof. exact (@lem2540945 n (@lem2540942 n h1)). Qed.
Lemma lem2540947 (n : int) : (term430 n) = (term291 n).
Proof. exact (@lem1982733 (term291 n)). Qed.
Lemma lem2540948 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2540949 (n : int) : (term431 n) = (term432 n).
Proof. exact (MK_COMB (@lem2540948) (@lem2540947 n)). Qed.
Lemma lem2540950 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2540951 (n : int) : (term429 n) = (term421 n).
Proof. exact (MK_COMB (@lem2540949 n) (@lem2540950)). Qed.
Lemma lem2540952 (n : int) (h1 : term376 n) : term421 n.
Proof. exact (EQ_MP (@lem2540951 n) (@lem2540946 n h1)). Qed.
Lemma lem2540953 (n : int) (h1 : term376 n) : term433 n.
Proof. exact (conj (@lem2540952 n h1) (@lem2540878 n h1)). Qed.
Lemma lem2540955 (x : real) (y : real) : term413 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2540956 (n : int) : term434 n.
Proof. exact (@lem2540955 (term291 n) (term277 n)). Qed.
Lemma lem2540957 (n : int) (h1 : term376 n) : term435 n.
Proof. exact (@lem2540956 n (@lem2540953 n h1)). Qed.
Lemma lem2540958 (n : int) : (term436 n) = (term417 n).
Proof. exact (@lem1982763 (term291 n) (real_of_int n) term243). Qed.
Lemma lem2540959 (n : int) : (term418 n) = (term293 n).
Proof. exact (@lem1982713 term243 (real_of_int n)). Qed.
Lemma lem2540961 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2540962 : term159 = term245.
Proof. exact (@lem2540961 term160). Qed.
Lemma lem2540964 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2540965 : term243 = term248.
Proof. exact (@lem2540964 term160). Qed.
Lemma lem2540966 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2540967 : term294 = term295.
Proof. exact (MK_COMB (@lem2540966) (@lem2540965)). Qed.
Lemma lem2540968 : term296 = term297.
Proof. exact (MK_COMB (@lem2540967) (@lem2540962)). Qed.
Lemma lem2540969 : term298.
Proof. exact (@lem1981473 term243 term159 term159 term159 term166 term159). Qed.
Lemma lem2540971 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540972 : term300 = term301.
Proof. exact (@lem2540971 (NUMERAL 0) term160). Qed.
Lemma lem2540973 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540974 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540975 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540974 h1) (fun h1 : term301 = True => @lem2540973)). Qed.
Lemma lem2540976 : term301 = True.
Proof. exact (EQ_MP (@lem2540975) (@lem2540973)). Qed.
Lemma lem2540977 : term300 = True.
Proof. exact (TRANS (@lem2540972) (@lem2540976)). Qed.
Lemma lem2540978 : True = term300.
Proof. exact (SYM (@lem2540977)). Qed.
Lemma lem2540979 : term300.
Proof. exact (EQ_MP (@lem2540978) (@lem0)). Qed.
Lemma lem2540980 : term303.
Proof. exact (@lem2540969 (@lem2540979)). Qed.
Lemma lem2540982 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540983 : term300 = term301.
Proof. exact (@lem2540982 (NUMERAL 0) term160). Qed.
Lemma lem2540984 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540985 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540986 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540985 h1) (fun h1 : term301 = True => @lem2540984)). Qed.
Lemma lem2540987 : term301 = True.
Proof. exact (EQ_MP (@lem2540986) (@lem2540984)). Qed.
Lemma lem2540988 : term300 = True.
Proof. exact (TRANS (@lem2540983) (@lem2540987)). Qed.
Lemma lem2540989 : True = term300.
Proof. exact (SYM (@lem2540988)). Qed.
Lemma lem2540990 : term300.
Proof. exact (EQ_MP (@lem2540989) (@lem0)). Qed.
Lemma lem2540991 : term304.
Proof. exact (@lem2540980 (@lem2540990)). Qed.
Lemma lem2540993 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2540994 : term300 = term301.
Proof. exact (@lem2540993 (NUMERAL 0) term160). Qed.
Lemma lem2540995 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2540996 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2540997 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2540996 h1) (fun h1 : term301 = True => @lem2540995)). Qed.
Lemma lem2540998 : term301 = True.
Proof. exact (EQ_MP (@lem2540997) (@lem2540995)). Qed.
Lemma lem2540999 : term300 = True.
Proof. exact (TRANS (@lem2540994) (@lem2540998)). Qed.
Lemma lem2541000 : True = term300.
Proof. exact (SYM (@lem2540999)). Qed.
Lemma lem2541001 : term300.
Proof. exact (EQ_MP (@lem2541000) (@lem0)). Qed.
Lemma lem2541002 : term305.
Proof. exact (@lem2540991 (@lem2541001)). Qed.
Lemma lem2541004 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2541005 : term256 = term257.
Proof. exact (@lem2541004 term160 term160). Qed.
Lemma lem2541006 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2541007 : term259 = term160.
Proof. exact (EQ_MP (@lem2541006) (@lem940073)). Qed.
Lemma lem2541008 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2541009 : term257 = term159.
Proof. exact (MK_COMB (@lem2541008) (@lem2541007)). Qed.
Lemma lem2541010 : term256 = term159.
Proof. exact (TRANS (@lem2541005) (@lem2541009)). Qed.
Lemma lem2541012 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2541013 : term251 = term262.
Proof. exact (@lem2541012 term160 term160). Qed.
Lemma lem2541014 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2541015 : term259 = term160.
Proof. exact (EQ_MP (@lem2541014) (@lem940073)). Qed.
Lemma lem2541016 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2541017 : term257 = term159.
Proof. exact (MK_COMB (@lem2541016) (@lem2541015)). Qed.
Lemma lem2541018 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2541019 : term262 = term243.
Proof. exact (MK_COMB (@lem2541018) (@lem2541017)). Qed.
Lemma lem2541020 : term251 = term243.
Proof. exact (TRANS (@lem2541013) (@lem2541019)). Qed.
Lemma lem2541021 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2541022 : term306 = term294.
Proof. exact (MK_COMB (@lem2541021) (@lem2541020)). Qed.
Lemma lem2541023 : term307 = term296.
Proof. exact (MK_COMB (@lem2541022) (@lem2541010)). Qed.
Lemma lem2541025 (m : nat) : (term308 m) = term166.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2541026 : term296 = term166.
Proof. exact (@lem2541025 term160). Qed.
Lemma lem2541027 : term307 = term166.
Proof. exact (TRANS (@lem2541023) (@lem2541026)). Qed.
Lemma lem2541028 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2541029 : term309 = term310.
Proof. exact (MK_COMB (@lem2541028) (@lem2541027)). Qed.
Lemma lem2541030 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2541031 : term311 = term312.
Proof. exact (MK_COMB (@lem2541029) (@lem2541030)). Qed.
Lemma lem2541033 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2541034 : term312 = term166.
Proof. exact (@lem2541033 term160). Qed.
Lemma lem2541035 : term311 = term166.
Proof. exact (TRANS (@lem2541031) (@lem2541034)). Qed.
Lemma lem2541037 (m : nat) (n : nat) : (term254 m n) = (term255 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2541038 : term256 = term257.
Proof. exact (@lem2541037 term160 term160). Qed.
Lemma lem2541039 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2541040 : term259 = term160.
Proof. exact (EQ_MP (@lem2541039) (@lem940073)). Qed.
Lemma lem2541041 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2541042 : term257 = term159.
Proof. exact (MK_COMB (@lem2541041) (@lem2541040)). Qed.
Lemma lem2541043 : term256 = term159.
Proof. exact (TRANS (@lem2541038) (@lem2541042)). Qed.
Lemma lem2541044 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem2541045 : term314 = term312.
Proof. exact (MK_COMB (@lem2541044) (@lem2541043)). Qed.
Lemma lem2541047 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2541048 : term312 = term166.
Proof. exact (@lem2541047 term160). Qed.
Lemma lem2541049 : term314 = term166.
Proof. exact (TRANS (@lem2541045) (@lem2541048)). Qed.
Lemma lem2541050 : term166 = term314.
Proof. exact (SYM (@lem2541049)). Qed.
Lemma lem2541051 : term311 = term314.
Proof. exact (TRANS (@lem2541035) (@lem2541050)). Qed.
Lemma lem2541052 : term297 = term315.
Proof. exact (@lem2541002 (@lem2541051)). Qed.
Lemma lem2541053 : term296 = term315.
Proof. exact (TRANS (@lem2540968) (@lem2541052)). Qed.
Lemma lem2541055 (x : real) : (term265 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2541056 : term315 = term166.
Proof. exact (@lem2541055 term166). Qed.
Lemma lem2541057 : term296 = term166.
Proof. exact (TRANS (@lem2541053) (@lem2541056)). Qed.
Lemma lem2541058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2541059 : term316 = term310.
Proof. exact (MK_COMB (@lem2541058) (@lem2541057)). Qed.
Lemma lem2541060 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2541061 (n : int) : (term293 n) = (term317 n).
Proof. exact (MK_COMB (@lem2541059) (@lem2541060 n)). Qed.
Lemma lem2541062 (n : int) : (term418 n) = (term317 n).
Proof. exact (TRANS (@lem2540959 n) (@lem2541061 n)). Qed.
Lemma lem2541063 (n : int) : (term317 n) = term166.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2541064 (n : int) : (term418 n) = term166.
Proof. exact (TRANS (@lem2541062 n) (@lem2541063 n)). Qed.
Lemma lem2541065 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2541066 (n : int) : (term419 n) = term176.
Proof. exact (MK_COMB (@lem2541065) (@lem2541064 n)). Qed.
Lemma lem2541067 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem2541068 (n : int) : (term417 n) = term319.
Proof. exact (MK_COMB (@lem2541066 n) (@lem2541067)). Qed.
Lemma lem2541069 (n : int) : (term436 n) = term319.
Proof. exact (TRANS (@lem2540958 n) (@lem2541068 n)). Qed.
Lemma lem2541070 : term319 = term243.
Proof. exact (@lem1982721 term243). Qed.
Lemma lem2541071 (n : int) : (term436 n) = term243.
Proof. exact (TRANS (@lem2541069 n) (@lem2541070)). Qed.
Lemma lem2541072 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2541073 (n : int) : (term437 n) = term321.
Proof. exact (MK_COMB (@lem2541072) (@lem2541071 n)). Qed.
Lemma lem2541074 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2541075 (n : int) : (term435 n) = term322.
Proof. exact (MK_COMB (@lem2541073 n) (@lem2541074)). Qed.
Lemma lem2541076 (n : int) (h1 : term376 n) : term322.
Proof. exact (EQ_MP (@lem2541075 n) (@lem2540957 n h1)). Qed.
Lemma lem2541078 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2541079 : term322 = term383.
Proof. exact (@lem2541078 term166 term243). Qed.
Lemma lem2541081 (x : nat) : (term246 x) = (term247 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2541082 : term243 = term248.
Proof. exact (@lem2541081 term160). Qed.
Lemma lem2541084 (x : nat) : (real_of_num x) = (term244 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2541085 : term166 = term315.
Proof. exact (@lem2541084 (NUMERAL 0)). Qed.
Lemma lem2541086 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2541087 : term384 = term385.
Proof. exact (MK_COMB (@lem2541086) (@lem2541085)). Qed.
Lemma lem2541088 : term383 = term386.
Proof. exact (MK_COMB (@lem2541087) (@lem2541082)). Qed.
Lemma lem2541089 : term387.
Proof. exact (@lem1980026 term166 term159 term243 term159). Qed.
Lemma lem2541091 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2541092 : term300 = term301.
Proof. exact (@lem2541091 (NUMERAL 0) term160). Qed.
Lemma lem2541093 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2541094 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2541095 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2541094 h1) (fun h1 : term301 = True => @lem2541093)). Qed.
Lemma lem2541096 : term301 = True.
Proof. exact (EQ_MP (@lem2541095) (@lem2541093)). Qed.
Lemma lem2541097 : term300 = True.
Proof. exact (TRANS (@lem2541092) (@lem2541096)). Qed.
Lemma lem2541098 : True = term300.
Proof. exact (SYM (@lem2541097)). Qed.
Lemma lem2541099 : term300.
Proof. exact (EQ_MP (@lem2541098) (@lem0)). Qed.
Lemma lem2541100 : term388.
Proof. exact (@lem2541089 (@lem2541099)). Qed.
Lemma lem2541102 (m : nat) (n : nat) : (term299 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2541103 : term300 = term301.
Proof. exact (@lem2541102 (NUMERAL 0) term160). Qed.
Lemma lem2541104 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2541105 (h1 : term302 = (BIT1 0)) : term301 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2541106 : (term302 = (BIT1 0)) = (term301 = True).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2541105 h1) (fun h1 : term301 = True => @lem2541104)). Qed.
Lemma lem2541107 : term301 = True.
Proof. exact (EQ_MP (@lem2541106) (@lem2541104)). Qed.
Lemma lem2541108 : term300 = True.
Proof. exact (TRANS (@lem2541103) (@lem2541107)). Qed.
Lemma lem2541109 : True = term300.
Proof. exact (SYM (@lem2541108)). Qed.
Lemma lem2541110 : term300.
Proof. exact (EQ_MP (@lem2541109) (@lem0)). Qed.
Lemma lem2541111 : term386 = term389.
Proof. exact (@lem2541100 (@lem2541110)). Qed.
Lemma lem2541113 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2541114 : term251 = term262.
Proof. exact (@lem2541113 term160 term160). Qed.
Lemma lem2541115 : (term258 = (BIT1 0)) = (term259 = term160).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2541116 : term259 = term160.
Proof. exact (EQ_MP (@lem2541115) (@lem940073)). Qed.
Lemma lem2541117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2541118 : term257 = term159.
Proof. exact (MK_COMB (@lem2541117) (@lem2541116)). Qed.
Lemma lem2541119 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2541120 : term262 = term243.
Proof. exact (MK_COMB (@lem2541119) (@lem2541118)). Qed.
Lemma lem2541121 : term251 = term243.
Proof. exact (TRANS (@lem2541114) (@lem2541120)). Qed.
Lemma lem2541123 (x : nat) : (term313 x) = term166.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2541124 : term312 = term166.
Proof. exact (@lem2541123 term160). Qed.
Lemma lem2541125 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2541126 : term390 = term384.
Proof. exact (MK_COMB (@lem2541125) (@lem2541124)). Qed.
Lemma lem2541127 : term389 = term383.
Proof. exact (MK_COMB (@lem2541126) (@lem2541121)). Qed.
Lemma lem2541129 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2541130 : term383 = term393.
Proof. exact (@lem2541129 (NUMERAL 0) term160). Qed.
Lemma lem2541131 : term302 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2541132 (h1 : term302 = (BIT1 0)) : (term160 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2541133 : (term302 = (BIT1 0)) = ((term160 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term302 = (BIT1 0) => @lem2541132 h1) (fun h1 : (term160 = (NUMERAL 0)) = False => @lem2541131)). Qed.
Lemma lem2541134 : (term160 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2541133) (@lem2541131)). Qed.
Lemma lem2541135 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2541136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2541137 : term394 = (and True).
Proof. exact (MK_COMB (@lem2541136) (@lem2541135)). Qed.
Lemma lem2541138 : term393 = (True /\ False).
Proof. exact (MK_COMB (@lem2541137) (@lem2541134)). Qed.
Lemma lem2541140 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2541141 : term393 = False.
Proof. exact (TRANS (@lem2541138) (@lem2541140)). Qed.
Lemma lem2541142 : term383 = False.
Proof. exact (TRANS (@lem2541130) (@lem2541141)). Qed.
Lemma lem2541143 : term389 = False.
Proof. exact (TRANS (@lem2541127) (@lem2541142)). Qed.
Lemma lem2541144 : term386 = False.
Proof. exact (TRANS (@lem2541111) (@lem2541143)). Qed.
Lemma lem2541145 : term383 = False.
Proof. exact (TRANS (@lem2541088) (@lem2541144)). Qed.
Lemma lem2541146 : term322 = False.
Proof. exact (TRANS (@lem2541079) (@lem2541145)). Qed.
Lemma lem2541147 (n : int) (h1 : term376 n) : False.
Proof. exact (EQ_MP (@lem2541146) (@lem2541076 n h1)). Qed.
Lemma lem2541148 (n : int) (h1 : term379 n) : False.
Proof. exact (or_elim (@lem2540451 n h1) (fun h0 : term373 n => @lem2540799 n h0) (fun h0 : term376 n => @lem2541147 n h0)). Qed.
Lemma lem2541149 (n : int) (h1 : term380 n) : False.
Proof. exact (or_elim (@lem2540300 n h1) (fun h0 : term352 n => @lem2540450 n h0) (fun h0 : term379 n => @lem2541148 n h0)). Qed.
Lemma lem2541150 (n : int) (h1 : term381 n) : False.
Proof. exact (or_elim (@lem2539997 n h1) (fun h0 : term358 n => @lem2540299 n h0) (fun h0 : term380 n => @lem2541149 n h0)). Qed.
Lemma lem2541151 (n : int) (h1 : term361 n) : term361 n.
Proof. exact (h1). Qed.
Lemma lem2541152 (n : int) (h1 : term361 n) : term381 n.
Proof. exact (EQ_MP (@lem2539996 n) (@lem2541151 n h1)). Qed.
Lemma lem2541153 (n : int) (h1 : term361 n) : (term381 n) = False.
Proof. exact (prop_ext (fun h2 : term381 n => @lem2541150 n h2) (fun h2 : False => @lem2541152 n h1)). Qed.
Lemma lem2541154 (n : int) (h1 : term361 n) : False.
Proof. exact (EQ_MP (@lem2541153 n h1) (@lem2541152 n h1)). Qed.
Lemma lem2541155 (n : int) (h1 : term237 n) : term237 n.
Proof. exact (h1). Qed.
Lemma lem2541156 (n : int) (h1 : term237 n) : term361 n.
Proof. exact (EQ_MP (@lem2539891 n) (@lem2541155 n h1)). Qed.
Lemma lem2541157 (n : int) (h1 : term237 n) : (term361 n) = False.
Proof. exact (prop_ext (fun h2 : term361 n => @lem2541154 n h2) (fun h2 : False => @lem2541156 n h1)). Qed.
Lemma lem2541158 (n : int) (h1 : term237 n) : False.
Proof. exact (EQ_MP (@lem2541157 n h1) (@lem2541156 n h1)). Qed.
Lemma lem2541159 (n : int) : term438 n.
Proof. exact (fun h0 : term237 n => @lem2541158 n h0). Qed.
Lemma lem2541160 (n : int) : term439 n.
Proof. exact (@lem1386578 (term440 n)). Qed.
Lemma lem2541163 (n : int) : term440 n.
Proof. exact (@lem2541160 n (@lem2541159 n)). Qed.
Lemma lem2541164 (n : int) : (term235 n) = (term144 n).
Proof. exact (SYM (@lem2539149 n)). Qed.
Lemma lem2541165 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2541166 (n : int) : (term440 n) = (term129 n).
Proof. exact (MK_COMB (@lem2541165) (@lem2541164 n)). Qed.
Lemma lem2541167 (n : int) : term129 n.
Proof. exact (EQ_MP (@lem2541166 n) (@lem2541163 n)). Qed.
Lemma lem2541168 (n : int) : term130 n.
Proof. exact (EQ_MP (@lem2538912 n) (@lem2541167 n)). Qed.
Lemma lem2541169 (n : int) : (term130 n) = ((term130 n) = True).
Proof. exact (@lem7 (term130 n)). Qed.
Lemma lem2541170 (n : int) : (term130 n) = True.
Proof. exact (EQ_MP (@lem2541169 n) (@lem2541168 n)). Qed.
Lemma lem2541171 (n : int) : True = (term130 n).
Proof. exact (SYM (@lem2541170 n)). Qed.
Lemma lem2541172 (n : int) : term130 n.
Proof. exact (EQ_MP (@lem2541171 n) (@lem0)). Qed.
Lemma lem2541173 (n : int) (h1 : term75 n) : term145 n.
Proof. exact (@lem2541172 n (@lem2538236 n h1)). Qed.
Lemma lem2541175 (n : int) (h1 : term75 n) : term61 n.
Proof. exact (@lem2538911 n (@lem2541173 n h1)). Qed.
Lemma lem2541176 (n : int) (h1 : term75 n) : (term75 n) = (term61 n).
Proof. exact (prop_ext (fun h2 : term75 n => @lem2541175 n h1) (fun h2 : term61 n => @lem2538236 n h1)). Qed.
Lemma lem2541177 (n : int) (h1 : term75 n) : term61 n.
Proof. exact (EQ_MP (@lem2541176 n h1) (@lem2538236 n h1)). Qed.
Lemma lem2541178 (n : int) : term64 n.
Proof. exact (fun h0 : term75 n => @lem2541177 n h0). Qed.
Lemma lem2541179 (n : int) (h1 : n = term38) : term66 n.
Proof. exact (EQ_MP (@lem2538256 n) (@lem2538907 n h1)). Qed.
Lemma lem2541180 (n : int) (h1 : n = term38) : (n = term38) = (term66 n).
Proof. exact (prop_ext (fun h2 : n = term38 => @lem2541179 n h1) (fun h2 : term66 n => @lem2538219 n h1)). Qed.
Lemma lem2541181 (n : int) (h1 : n = term38) : term66 n.
Proof. exact (EQ_MP (@lem2541180 n h1) (@lem2538219 n h1)). Qed.
Lemma lem2541182 (n : int) : term69 n.
Proof. exact (fun h0 : n = term38 => @lem2541181 n h0). Qed.
Lemma lem2541183 (n : int) : term72 n.
Proof. exact (conj (@lem2541182 n) (@lem2541178 n)). Qed.
Lemma lem2541184 (n : int) : term48 n.
Proof. exact (EQ_MP (@lem2538218 n) (@lem2541183 n)). Qed.
Lemma lem2541189 : term51.
Proof. exact (fun n : int => @lem2541184 n). Qed.
Lemma lem2541190 : term42.
Proof. exact (EQ_MP (@lem2538200) (@lem2541189)). Qed.
