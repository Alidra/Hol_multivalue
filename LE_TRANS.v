Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_TRANS_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_SUC_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Lemma lem93081 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem93082 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem93083 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem93082 n) (@lem93081 n)). Qed.
Lemma lem93084 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem93104 : term3.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem93105 (m : nat) : term4 m.
Proof. exact (@lem93104 m). Qed.
Lemma lem93106 (m : nat) : (term4 m) = ((term5 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem93109 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93110 : term7.
Proof. exact (@lem93109 term8). Qed.
Lemma lem93111 : term9 = term10.
Proof. exact (eq_refl term9). Qed.
Lemma lem93112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93113 : term11 = term12.
Proof. exact (MK_COMB (@lem93112) (@lem93111)). Qed.
Lemma lem93114 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem93115 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93116 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem93115) (@lem93114 m)). Qed.
Lemma lem93117 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem93118 (m : nat) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem93116 m) (@lem93117 m)). Qed.
Lemma lem93119 : term21 = term22.
Proof. exact (fun_ext (fun m : nat => @lem93118 m)). Qed.
Lemma lem93120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93121 : term23 = term24.
Proof. exact (MK_COMB (@lem93120) (@lem93119)). Qed.
Lemma lem93122 : term25 = term26.
Proof. exact (MK_COMB (@lem93113) (@lem93121)). Qed.
Lemma lem93123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93124 : term27 = term28.
Proof. exact (MK_COMB (@lem93123) (@lem93122)). Qed.
Lemma lem93125 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem93126 : term29 = term8.
Proof. exact (fun_ext (fun m : nat => @lem93125 m)). Qed.
Lemma lem93127 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93128 : term30 = term31.
Proof. exact (MK_COMB (@lem93127) (@lem93126)). Qed.
Lemma lem93129 : term7 = term32.
Proof. exact (MK_COMB (@lem93124) (@lem93128)). Qed.
Lemma lem93130 : term32.
Proof. exact (EQ_MP (@lem93129) (@lem93110)). Qed.
Lemma lem93131 (m : nat) (h1 : term14 m) : term14 m.
Proof. exact (h1). Qed.
Lemma lem93133 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93134 : term33.
Proof. exact (@lem93133 term34). Qed.
Lemma lem93135 : term35 = term36.
Proof. exact (eq_refl term35). Qed.
Lemma lem93136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93137 : term37 = term38.
Proof. exact (MK_COMB (@lem93136) (@lem93135)). Qed.
Lemma lem93138 (n : nat) : (term39 n) = (term40 n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem93139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93140 (n : nat) : (term41 n) = (term42 n).
Proof. exact (MK_COMB (@lem93139) (@lem93138 n)). Qed.
Lemma lem93141 (n : nat) : (term43 n) = (term44 n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem93142 (n : nat) : (term45 n) = (term46 n).
Proof. exact (MK_COMB (@lem93140 n) (@lem93141 n)). Qed.
Lemma lem93143 : term47 = term48.
Proof. exact (fun_ext (fun n : nat => @lem93142 n)). Qed.
Lemma lem93144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93145 : term49 = term50.
Proof. exact (MK_COMB (@lem93144) (@lem93143)). Qed.
Lemma lem93146 : term51 = term52.
Proof. exact (MK_COMB (@lem93137) (@lem93145)). Qed.
Lemma lem93147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93148 : term53 = term54.
Proof. exact (MK_COMB (@lem93147) (@lem93146)). Qed.
Lemma lem93149 (n : nat) : (term39 n) = (term40 n).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem93150 : term55 = term34.
Proof. exact (fun_ext (fun n : nat => @lem93149 n)). Qed.
Lemma lem93151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93152 : term56 = term10.
Proof. exact (MK_COMB (@lem93151) (@lem93150)). Qed.
Lemma lem93153 : term33 = term57.
Proof. exact (MK_COMB (@lem93148) (@lem93152)). Qed.
Lemma lem93154 : term57.
Proof. exact (EQ_MP (@lem93153) (@lem93134)). Qed.
Lemma lem93157 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93158 : term58.
Proof. exact (@lem93157 term59). Qed.
Lemma lem93159 : term60 = term61.
Proof. exact (eq_refl term60). Qed.
Lemma lem93160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93161 : term62 = term63.
Proof. exact (MK_COMB (@lem93160) (@lem93159)). Qed.
Lemma lem93162 (p : nat) : (term64 p) = (term65 p).
Proof. exact (eq_refl (term64 p)). Qed.
Lemma lem93163 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93164 (p : nat) : (term66 p) = (term67 p).
Proof. exact (MK_COMB (@lem93163) (@lem93162 p)). Qed.
Lemma lem93165 (p : nat) : (term68 p) = (term69 p).
Proof. exact (eq_refl (term68 p)). Qed.
Lemma lem93166 (p : nat) : (term70 p) = (term71 p).
Proof. exact (MK_COMB (@lem93164 p) (@lem93165 p)). Qed.
Lemma lem93167 : term72 = term73.
Proof. exact (fun_ext (fun p : nat => @lem93166 p)). Qed.
Lemma lem93168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93169 : term74 = term75.
Proof. exact (MK_COMB (@lem93168) (@lem93167)). Qed.
Lemma lem93170 : term76 = term77.
Proof. exact (MK_COMB (@lem93161) (@lem93169)). Qed.
Lemma lem93171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93172 : term78 = term79.
Proof. exact (MK_COMB (@lem93171) (@lem93170)). Qed.
Lemma lem93173 (p : nat) : (term64 p) = (term65 p).
Proof. exact (eq_refl (term64 p)). Qed.
Lemma lem93174 : term80 = term59.
Proof. exact (fun_ext (fun p : nat => @lem93173 p)). Qed.
Lemma lem93175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93176 : term81 = term36.
Proof. exact (MK_COMB (@lem93175) (@lem93174)). Qed.
Lemma lem93177 : term58 = term82.
Proof. exact (MK_COMB (@lem93172) (@lem93176)). Qed.
Lemma lem93178 : term82.
Proof. exact (EQ_MP (@lem93177) (@lem93158)). Qed.
Lemma lem93185 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93186 (n : nat) : term83 n.
Proof. exact (@lem93185 (term84 n)). Qed.
Lemma lem93187 (n : nat) : (term85 n) = (term86 n).
Proof. exact (eq_refl (term85 n)). Qed.
Lemma lem93188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93189 (n : nat) : (term87 n) = (term88 n).
Proof. exact (MK_COMB (@lem93188) (@lem93187 n)). Qed.
Lemma lem93190 (n : nat) (p : nat) : (term89 n p) = (term90 n p).
Proof. exact (eq_refl (term89 n p)). Qed.
Lemma lem93191 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93192 (n : nat) (p : nat) : (term91 n p) = (term92 n p).
Proof. exact (MK_COMB (@lem93191) (@lem93190 n p)). Qed.
Lemma lem93193 (n : nat) (p : nat) : (term93 n p) = (term94 n p).
Proof. exact (eq_refl (term93 n p)). Qed.
Lemma lem93194 (n : nat) (p : nat) : (term95 n p) = (term96 n p).
Proof. exact (MK_COMB (@lem93192 n p) (@lem93193 n p)). Qed.
Lemma lem93195 (n : nat) : (term97 n) = (term98 n).
Proof. exact (fun_ext (fun p : nat => @lem93194 n p)). Qed.
Lemma lem93196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93197 (n : nat) : (term99 n) = (term100 n).
Proof. exact (MK_COMB (@lem93196) (@lem93195 n)). Qed.
Lemma lem93198 (n : nat) : (term101 n) = (term102 n).
Proof. exact (MK_COMB (@lem93189 n) (@lem93197 n)). Qed.
Lemma lem93199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93200 (n : nat) : (term103 n) = (term104 n).
Proof. exact (MK_COMB (@lem93199) (@lem93198 n)). Qed.
Lemma lem93201 (n : nat) (p : nat) : (term89 n p) = (term90 n p).
Proof. exact (eq_refl (term89 n p)). Qed.
Lemma lem93202 (n : nat) : (term105 n) = (term84 n).
Proof. exact (fun_ext (fun p : nat => @lem93201 n p)). Qed.
Lemma lem93203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93204 (n : nat) : (term106 n) = (term44 n).
Proof. exact (MK_COMB (@lem93203) (@lem93202 n)). Qed.
Lemma lem93205 (n : nat) : (term83 n) = (term107 n).
Proof. exact (MK_COMB (@lem93200 n) (@lem93204 n)). Qed.
Lemma lem93206 (n : nat) : term107 n.
Proof. exact (EQ_MP (@lem93205 n) (@lem93186 n)). Qed.
Lemma lem93213 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93214 (m : nat) : term108 m.
Proof. exact (@lem93213 (term109 m)). Qed.
Lemma lem93215 (m : nat) : (term110 m) = (term111 m).
Proof. exact (eq_refl (term110 m)). Qed.
Lemma lem93216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93217 (m : nat) : (term112 m) = (term113 m).
Proof. exact (MK_COMB (@lem93216) (@lem93215 m)). Qed.
Lemma lem93218 (n : nat) (m : nat) : (term114 m n) = (term115 n m).
Proof. exact (eq_refl (term114 m n)). Qed.
Lemma lem93219 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93220 (n : nat) (m : nat) : (term116 m n) = (term117 n m).
Proof. exact (MK_COMB (@lem93219) (@lem93218 n m)). Qed.
Lemma lem93221 (n : nat) (m : nat) : (term118 m n) = (term119 n m).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem93222 (n : nat) (m : nat) : (term120 m n) = (term121 n m).
Proof. exact (MK_COMB (@lem93220 n m) (@lem93221 n m)). Qed.
Lemma lem93223 (m : nat) : (term122 m) = (term123 m).
Proof. exact (fun_ext (fun n : nat => @lem93222 n m)). Qed.
Lemma lem93224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93225 (m : nat) : (term124 m) = (term125 m).
Proof. exact (MK_COMB (@lem93224) (@lem93223 m)). Qed.
Lemma lem93226 (m : nat) : (term126 m) = (term127 m).
Proof. exact (MK_COMB (@lem93217 m) (@lem93225 m)). Qed.
Lemma lem93227 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93228 (m : nat) : (term128 m) = (term129 m).
Proof. exact (MK_COMB (@lem93227) (@lem93226 m)). Qed.
Lemma lem93229 (n : nat) (m : nat) : (term114 m n) = (term115 n m).
Proof. exact (eq_refl (term114 m n)). Qed.
Lemma lem93230 (m : nat) : (term130 m) = (term109 m).
Proof. exact (fun_ext (fun n : nat => @lem93229 n m)). Qed.
Lemma lem93231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93232 (m : nat) : (term131 m) = (term18 m).
Proof. exact (MK_COMB (@lem93231) (@lem93230 m)). Qed.
Lemma lem93233 (m : nat) : (term108 m) = (term132 m).
Proof. exact (MK_COMB (@lem93228 m) (@lem93232 m)). Qed.
Lemma lem93234 (m : nat) : term132 m.
Proof. exact (EQ_MP (@lem93233 m) (@lem93214 m)). Qed.
Lemma lem93237 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93238 (m : nat) : term133 m.
Proof. exact (@lem93237 (term134 m)). Qed.
Lemma lem93239 (m : nat) : (term135 m) = (term136 m).
Proof. exact (eq_refl (term135 m)). Qed.
Lemma lem93240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93241 (m : nat) : (term137 m) = (term138 m).
Proof. exact (MK_COMB (@lem93240) (@lem93239 m)). Qed.
Lemma lem93242 (m : nat) (p : nat) : (term139 m p) = (term140 m p).
Proof. exact (eq_refl (term139 m p)). Qed.
Lemma lem93243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93244 (m : nat) (p : nat) : (term141 m p) = (term142 m p).
Proof. exact (MK_COMB (@lem93243) (@lem93242 m p)). Qed.
Lemma lem93245 (m : nat) (p : nat) : (term143 m p) = (term144 m p).
Proof. exact (eq_refl (term143 m p)). Qed.
Lemma lem93246 (m : nat) (p : nat) : (term145 m p) = (term146 m p).
Proof. exact (MK_COMB (@lem93244 m p) (@lem93245 m p)). Qed.
Lemma lem93247 (m : nat) : (term147 m) = (term148 m).
Proof. exact (fun_ext (fun p : nat => @lem93246 m p)). Qed.
Lemma lem93248 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93249 (m : nat) : (term149 m) = (term150 m).
Proof. exact (MK_COMB (@lem93248) (@lem93247 m)). Qed.
Lemma lem93250 (m : nat) : (term151 m) = (term152 m).
Proof. exact (MK_COMB (@lem93241 m) (@lem93249 m)). Qed.
Lemma lem93251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93252 (m : nat) : (term153 m) = (term154 m).
Proof. exact (MK_COMB (@lem93251) (@lem93250 m)). Qed.
Lemma lem93253 (m : nat) (p : nat) : (term139 m p) = (term140 m p).
Proof. exact (eq_refl (term139 m p)). Qed.
Lemma lem93254 (m : nat) : (term155 m) = (term134 m).
Proof. exact (fun_ext (fun p : nat => @lem93253 m p)). Qed.
Lemma lem93255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93256 (m : nat) : (term156 m) = (term111 m).
Proof. exact (MK_COMB (@lem93255) (@lem93254 m)). Qed.
Lemma lem93257 (m : nat) : (term133 m) = (term157 m).
Proof. exact (MK_COMB (@lem93252 m) (@lem93256 m)). Qed.
Lemma lem93258 (m : nat) : term157 m.
Proof. exact (EQ_MP (@lem93257 m) (@lem93238 m)). Qed.
Lemma lem93265 (P : nat -> Prop) : term6 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93266 (n : nat) (m : nat) : term158 n m.
Proof. exact (@lem93265 (term159 n m)). Qed.
Lemma lem93267 (n : nat) (m : nat) : (term160 n m) = (term161 n m).
Proof. exact (eq_refl (term160 n m)). Qed.
Lemma lem93268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93269 (n : nat) (m : nat) : (term162 n m) = (term163 n m).
Proof. exact (MK_COMB (@lem93268) (@lem93267 n m)). Qed.
Lemma lem93270 (n : nat) (m : nat) (p : nat) : (term164 n m p) = (term165 n m p).
Proof. exact (eq_refl (term164 n m p)). Qed.
Lemma lem93271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93272 (n : nat) (m : nat) (p : nat) : (term166 n m p) = (term167 n m p).
Proof. exact (MK_COMB (@lem93271) (@lem93270 n m p)). Qed.
Lemma lem93273 (n : nat) (m : nat) (p : nat) : (term168 n m p) = (term169 n m p).
Proof. exact (eq_refl (term168 n m p)). Qed.
Lemma lem93274 (n : nat) (m : nat) (p : nat) : (term170 n m p) = (term171 n m p).
Proof. exact (MK_COMB (@lem93272 n m p) (@lem93273 n m p)). Qed.
Lemma lem93275 (n : nat) (m : nat) : (term172 n m) = (term173 n m).
Proof. exact (fun_ext (fun p : nat => @lem93274 n m p)). Qed.
Lemma lem93276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93277 (n : nat) (m : nat) : (term174 n m) = (term175 n m).
Proof. exact (MK_COMB (@lem93276) (@lem93275 n m)). Qed.
Lemma lem93278 (n : nat) (m : nat) : (term176 n m) = (term177 n m).
Proof. exact (MK_COMB (@lem93269 n m) (@lem93277 n m)). Qed.
Lemma lem93279 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93280 (n : nat) (m : nat) : (term178 n m) = (term179 n m).
Proof. exact (MK_COMB (@lem93279) (@lem93278 n m)). Qed.
Lemma lem93281 (n : nat) (m : nat) (p : nat) : (term164 n m p) = (term165 n m p).
Proof. exact (eq_refl (term164 n m p)). Qed.
Lemma lem93282 (n : nat) (m : nat) : (term180 n m) = (term159 n m).
Proof. exact (fun_ext (fun p : nat => @lem93281 n m p)). Qed.
Lemma lem93283 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93284 (n : nat) (m : nat) : (term181 n m) = (term119 n m).
Proof. exact (MK_COMB (@lem93283) (@lem93282 n m)). Qed.
Lemma lem93285 (n : nat) (m : nat) : (term158 n m) = (term182 n m).
Proof. exact (MK_COMB (@lem93280 n m) (@lem93284 n m)). Qed.
Lemma lem93286 (n : nat) (m : nat) : term182 n m.
Proof. exact (EQ_MP (@lem93285 n m) (@lem93266 n m)). Qed.
Lemma lem93292 (n : nat) : term183 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem93293 (n : nat) : (term183 n) = (term184 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem93294 (n : nat) : term184 n.
Proof. exact (EQ_MP (@lem93293 n) (@lem93292 n)). Qed.
Lemma lem93295 (n : nat) : (term184 n) = ((term184 n) = True).
Proof. exact (@lem7 (term184 n)). Qed.
Lemma lem93306 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem93307 : term185 = term186.
Proof. exact (@lem93306 term186). Qed.
Lemma lem93309 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93295 n) (@lem93294 n)). Qed.
Lemma lem93310 : term186 = True.
Proof. exact (@lem93309 (NUMERAL 0)). Qed.
Lemma lem93311 : term185 = True.
Proof. exact (TRANS (@lem93307) (@lem93310)). Qed.
Lemma lem93312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93313 : term187 = (imp True).
Proof. exact (MK_COMB (@lem93312) (@lem93311)). Qed.
Lemma lem93315 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93295 n) (@lem93294 n)). Qed.
Lemma lem93316 : term186 = True.
Proof. exact (@lem93315 (NUMERAL 0)). Qed.
Lemma lem93317 : term61 = (True -> True).
Proof. exact (MK_COMB (@lem93313) (@lem93316)). Qed.
Lemma lem93319 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem93320 : (True -> True) = True.
Proof. exact (@lem93319 True). Qed.
Lemma lem93321 : term61 = True.
Proof. exact (TRANS (@lem93317) (@lem93320)). Qed.
Lemma lem93322 : True = term61.
Proof. exact (SYM (@lem93321)). Qed.
Lemma lem93323 : term61.
Proof. exact (EQ_MP (@lem93322) (@lem0)). Qed.
Lemma lem93324 (n : nat) : term183 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem93325 (n : nat) : (term183 n) = (term184 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem93326 (n : nat) : term184 n.
Proof. exact (EQ_MP (@lem93325 n) (@lem93324 n)). Qed.
Lemma lem93327 (n : nat) : (term184 n) = ((term184 n) = True).
Proof. exact (@lem7 (term184 n)). Qed.
Lemma lem93342 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93327 n) (@lem93326 n)). Qed.
Lemma lem93343 : term186 = True.
Proof. exact (@lem93342 (NUMERAL 0)). Qed.
Lemma lem93344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93345 : term188 = (and True).
Proof. exact (MK_COMB (@lem93344) (@lem93343)). Qed.
Lemma lem93347 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93327 n) (@lem93326 n)). Qed.
Lemma lem93348 (p : nat) : (term189 p) = True.
Proof. exact (@lem93347 (S p)). Qed.
Lemma lem93349 (p : nat) : (term190 p) = (True /\ True).
Proof. exact (MK_COMB (@lem93345) (@lem93348 p)). Qed.
Lemma lem93351 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem93352 : (True /\ True) = True.
Proof. exact (@lem93351 True). Qed.
Lemma lem93353 (p : nat) : (term190 p) = True.
Proof. exact (TRANS (@lem93349 p) (@lem93352)). Qed.
Lemma lem93354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93355 (p : nat) : (term191 p) = (imp True).
Proof. exact (MK_COMB (@lem93354) (@lem93353 p)). Qed.
Lemma lem93357 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93327 n) (@lem93326 n)). Qed.
Lemma lem93358 (p : nat) : (term189 p) = True.
Proof. exact (@lem93357 (S p)). Qed.
Lemma lem93359 (p : nat) : (term69 p) = (True -> True).
Proof. exact (MK_COMB (@lem93355 p) (@lem93358 p)). Qed.
Lemma lem93361 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem93362 : (True -> True) = True.
Proof. exact (@lem93361 True). Qed.
Lemma lem93363 (p : nat) : (term69 p) = True.
Proof. exact (TRANS (@lem93359 p) (@lem93362)). Qed.
Lemma lem93364 (p : nat) : True = (term69 p).
Proof. exact (SYM (@lem93363 p)). Qed.
Lemma lem93365 (p : nat) : term69 p.
Proof. exact (EQ_MP (@lem93364 p) (@lem0)). Qed.
Lemma lem93366 (n : nat) : term183 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem93367 (n : nat) : (term183 n) = (term184 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem93368 (n : nat) : term184 n.
Proof. exact (EQ_MP (@lem93367 n) (@lem93366 n)). Qed.
Lemma lem93369 (n : nat) : (term184 n) = ((term184 n) = True).
Proof. exact (@lem7 (term184 n)). Qed.
Lemma lem93387 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93369 n) (@lem93368 n)). Qed.
Lemma lem93388 (n : nat) : (term189 n) = True.
Proof. exact (@lem93387 (S n)). Qed.
Lemma lem93389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93390 (n : nat) : (term192 n) = (and True).
Proof. exact (MK_COMB (@lem93389) (@lem93388 n)). Qed.
Lemma lem93391 (n : nat) : (term193 n) = (term193 n).
Proof. exact (eq_refl (term193 n)). Qed.
Lemma lem93392 (n : nat) : (term194 n) = (term195 n).
Proof. exact (MK_COMB (@lem93390 n) (@lem93391 n)). Qed.
Lemma lem93394 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem93395 (n : nat) : (term195 n) = (term193 n).
Proof. exact (@lem93394 (term193 n)). Qed.
Lemma lem93396 (n : nat) : (term194 n) = (term193 n).
Proof. exact (TRANS (@lem93392 n) (@lem93395 n)). Qed.
Lemma lem93397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93398 (n : nat) : (term196 n) = (term197 n).
Proof. exact (MK_COMB (@lem93397) (@lem93396 n)). Qed.
Lemma lem93400 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93369 n) (@lem93368 n)). Qed.
Lemma lem93401 : term186 = True.
Proof. exact (@lem93400 (NUMERAL 0)). Qed.
Lemma lem93402 (n : nat) : (term86 n) = (term198 n).
Proof. exact (MK_COMB (@lem93398 n) (@lem93401)). Qed.
Lemma lem93404 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem93405 (n : nat) : (term198 n) = True.
Proof. exact (@lem93404 (term193 n)). Qed.
Lemma lem93406 (n : nat) : (term86 n) = True.
Proof. exact (TRANS (@lem93402 n) (@lem93405 n)). Qed.
Lemma lem93407 (n : nat) : True = (term86 n).
Proof. exact (SYM (@lem93406 n)). Qed.
Lemma lem93408 (n : nat) : term86 n.
Proof. exact (EQ_MP (@lem93407 n) (@lem0)). Qed.
Lemma lem93409 (n : nat) : term183 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem93410 (n : nat) : (term183 n) = (term184 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem93411 (n : nat) : term184 n.
Proof. exact (EQ_MP (@lem93410 n) (@lem93409 n)). Qed.
Lemma lem93412 (n : nat) : (term184 n) = ((term184 n) = True).
Proof. exact (@lem7 (term184 n)). Qed.
Lemma lem93414 (m : nat) : term199 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem93415 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem93416 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem93415 m) (@lem93414 m)). Qed.
Lemma lem93417 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem93416 m n). Qed.
Lemma lem93418 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem93432 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93412 n) (@lem93411 n)). Qed.
Lemma lem93433 (n : nat) : (term189 n) = True.
Proof. exact (@lem93432 (S n)). Qed.
Lemma lem93434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93435 (n : nat) : (term192 n) = (and True).
Proof. exact (MK_COMB (@lem93434) (@lem93433 n)). Qed.
Lemma lem93437 (m : nat) (n : nat) : (term202 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem93418 m n) (@lem93417 m n)). Qed.
Lemma lem93438 (n : nat) (p : nat) : (term202 n p) = (Peano.le n p).
Proof. exact (@lem93437 n p). Qed.
Lemma lem93439 (n : nat) (p : nat) : (term203 n p) = (term204 n p).
Proof. exact (MK_COMB (@lem93435 n) (@lem93438 n p)). Qed.
Lemma lem93441 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem93442 (n : nat) (p : nat) : (term204 n p) = (Peano.le n p).
Proof. exact (@lem93441 (Peano.le n p)). Qed.
Lemma lem93443 (n : nat) (p : nat) : (term203 n p) = (Peano.le n p).
Proof. exact (TRANS (@lem93439 n p) (@lem93442 n p)). Qed.
Lemma lem93444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93445 (n : nat) (p : nat) : (term205 n p) = (term206 n p).
Proof. exact (MK_COMB (@lem93444) (@lem93443 n p)). Qed.
Lemma lem93447 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93412 n) (@lem93411 n)). Qed.
Lemma lem93448 (p : nat) : (term189 p) = True.
Proof. exact (@lem93447 (S p)). Qed.
Lemma lem93449 (n : nat) (p : nat) : (term94 n p) = (term207 n p).
Proof. exact (MK_COMB (@lem93445 n p) (@lem93448 p)). Qed.
Lemma lem93451 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem93452 (n : nat) (p : nat) : (term207 n p) = True.
Proof. exact (@lem93451 (Peano.le n p)). Qed.
Lemma lem93453 (n : nat) (p : nat) : (term94 n p) = True.
Proof. exact (TRANS (@lem93449 n p) (@lem93452 n p)). Qed.
Lemma lem93454 (n : nat) (p : nat) : True = (term94 n p).
Proof. exact (SYM (@lem93453 n p)). Qed.
Lemma lem93455 (n : nat) (p : nat) : term94 n p.
Proof. exact (EQ_MP (@lem93454 n p) (@lem0)). Qed.
Lemma lem93456 (n : nat) : term183 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem93457 (n : nat) : (term183 n) = (term184 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem93458 (n : nat) : term184 n.
Proof. exact (EQ_MP (@lem93457 n) (@lem93456 n)). Qed.
Lemma lem93459 (n : nat) : (term184 n) = ((term184 n) = True).
Proof. exact (@lem7 (term184 n)). Qed.
Lemma lem93480 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93459 n) (@lem93458 n)). Qed.
Lemma lem93481 : term186 = True.
Proof. exact (@lem93480 (NUMERAL 0)). Qed.
Lemma lem93482 (m : nat) : (term208 m) = (term208 m).
Proof. exact (eq_refl (term208 m)). Qed.
Lemma lem93483 (m : nat) : (term209 m) = (term210 m).
Proof. exact (MK_COMB (@lem93482 m) (@lem93481)). Qed.
Lemma lem93485 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem93486 (m : nat) : (term210 m) = (term193 m).
Proof. exact (@lem93485 (term193 m)). Qed.
Lemma lem93487 (m : nat) : (term209 m) = (term193 m).
Proof. exact (TRANS (@lem93483 m) (@lem93486 m)). Qed.
Lemma lem93488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93489 (m : nat) : (term211 m) = (term197 m).
Proof. exact (MK_COMB (@lem93488) (@lem93487 m)). Qed.
Lemma lem93490 (m : nat) : (term193 m) = (term193 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem93491 (m : nat) : (term136 m) = (term212 m).
Proof. exact (MK_COMB (@lem93489 m) (@lem93490 m)). Qed.
Lemma lem93493 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem93494 (m : nat) : (term212 m) = True.
Proof. exact (@lem93493 (term193 m)). Qed.
Lemma lem93495 (m : nat) : (term136 m) = True.
Proof. exact (TRANS (@lem93491 m) (@lem93494 m)). Qed.
Lemma lem93496 (m : nat) : True = (term136 m).
Proof. exact (SYM (@lem93495 m)). Qed.
Lemma lem93497 (m : nat) : term136 m.
Proof. exact (EQ_MP (@lem93496 m) (@lem0)). Qed.
Lemma lem93498 (n : nat) : term183 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem93499 (n : nat) : (term183 n) = (term184 n).
Proof. exact (eq_refl (term183 n)). Qed.
Lemma lem93500 (n : nat) : term184 n.
Proof. exact (EQ_MP (@lem93499 n) (@lem93498 n)). Qed.
Lemma lem93501 (n : nat) : (term184 n) = ((term184 n) = True).
Proof. exact (@lem7 (term184 n)). Qed.
Lemma lem93503 (m : nat) : term199 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem93504 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem93505 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem93504 m) (@lem93503 m)). Qed.
Lemma lem93506 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem93505 m n). Qed.
Lemma lem93507 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem93524 (n : nat) : (term184 n) = True.
Proof. exact (EQ_MP (@lem93501 n) (@lem93500 n)). Qed.
Lemma lem93525 (p : nat) : (term189 p) = True.
Proof. exact (@lem93524 (S p)). Qed.
Lemma lem93526 (m : nat) : (term208 m) = (term208 m).
Proof. exact (eq_refl (term208 m)). Qed.
Lemma lem93527 (p : nat) (m : nat) : (term213 m p) = (term210 m).
Proof. exact (MK_COMB (@lem93526 m) (@lem93525 p)). Qed.
Lemma lem93529 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem93530 (m : nat) : (term210 m) = (term193 m).
Proof. exact (@lem93529 (term193 m)). Qed.
Lemma lem93531 (p : nat) (m : nat) : (term213 m p) = (term193 m).
Proof. exact (TRANS (@lem93527 p m) (@lem93530 m)). Qed.
Lemma lem93532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93533 (p : nat) (m : nat) : (term214 m p) = (term197 m).
Proof. exact (MK_COMB (@lem93532) (@lem93531 p m)). Qed.
Lemma lem93535 (m : nat) (n : nat) : (term202 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem93507 m n) (@lem93506 m n)). Qed.
Lemma lem93536 (m : nat) (p : nat) : (term202 m p) = (Peano.le m p).
Proof. exact (@lem93535 m p). Qed.
Lemma lem93537 (m : nat) (p : nat) : (term144 m p) = (term215 m p).
Proof. exact (MK_COMB (@lem93533 p m) (@lem93536 m p)). Qed.
Lemma lem93540 (m : nat) (p : nat) : (term215 m p) = (term144 m p).
Proof. exact (SYM (@lem93537 m p)). Qed.
Lemma lem93546 (m : nat) : term199 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem93547 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem93548 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem93547 m) (@lem93546 m)). Qed.
Lemma lem93549 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem93548 m n). Qed.
Lemma lem93550 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem93570 (m : nat) (n : nat) : (term202 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem93550 m n) (@lem93549 m n)). Qed.
Lemma lem93571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93572 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (MK_COMB (@lem93571) (@lem93570 m n)). Qed.
Lemma lem93573 (n : nat) : (term193 n) = (term193 n).
Proof. exact (eq_refl (term193 n)). Qed.
Lemma lem93574 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (MK_COMB (@lem93572 m n) (@lem93573 n)). Qed.
Lemma lem93577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93578 (m : nat) (n : nat) : (term220 m n) = (term221 m n).
Proof. exact (MK_COMB (@lem93577) (@lem93574 m n)). Qed.
Lemma lem93579 (m : nat) : (term193 m) = (term193 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem93580 (n : nat) (m : nat) : (term161 n m) = (term222 n m).
Proof. exact (MK_COMB (@lem93578 m n) (@lem93579 m)). Qed.
Lemma lem93583 (n : nat) (m : nat) : (term222 n m) = (term161 n m).
Proof. exact (SYM (@lem93580 n m)). Qed.
Lemma lem93589 (m : nat) : term199 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem93590 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem93591 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem93590 m) (@lem93589 m)). Qed.
Lemma lem93592 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem93591 m n). Qed.
Lemma lem93593 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem93595 (n : nat) (m : nat) (h1 : term14 m) : term223 m n.
Proof. exact (@lem93131 m h1 n). Qed.
Lemma lem93596 (n : nat) (m : nat) : (term223 m n) = (term224 n m).
Proof. exact (eq_refl (term223 m n)). Qed.
Lemma lem93597 (n : nat) (m : nat) (h1 : term14 m) : term224 n m.
Proof. exact (EQ_MP (@lem93596 n m) (@lem93595 n m h1)). Qed.
Lemma lem93598 (n : nat) (p : nat) (m : nat) (h1 : term14 m) : term225 n m p.
Proof. exact (@lem93597 n m h1 p). Qed.
Lemma lem93599 (n : nat) (m : nat) (p : nat) : (term225 n m p) = (term226 n m p).
Proof. exact (eq_refl (term225 n m p)). Qed.
Lemma lem93600 (n : nat) (p : nat) (m : nat) (h1 : term14 m) : term226 n m p.
Proof. exact (EQ_MP (@lem93599 n m p) (@lem93598 n p m h1)). Qed.
Lemma lem93601 (n : nat) (m : nat) (p : nat) : (term226 n m p) = ((term226 n m p) = True).
Proof. exact (@lem7 (term226 n m p)). Qed.
Lemma lem93615 (m : nat) (n : nat) : (term202 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem93593 m n) (@lem93592 m n)). Qed.
Lemma lem93616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93617 (m : nat) (n : nat) : (term216 m n) = (term217 m n).
Proof. exact (MK_COMB (@lem93616) (@lem93615 m n)). Qed.
Lemma lem93619 (m : nat) (n : nat) : (term202 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem93593 m n) (@lem93592 m n)). Qed.
Lemma lem93620 (n : nat) (p : nat) : (term202 n p) = (Peano.le n p).
Proof. exact (@lem93619 n p). Qed.
Lemma lem93621 (m : nat) (n : nat) (p : nat) : (term227 m n p) = (term228 m n p).
Proof. exact (MK_COMB (@lem93617 m n) (@lem93620 n p)). Qed.
Lemma lem93624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93625 (m : nat) (n : nat) (p : nat) : (term229 m n p) = (term230 m n p).
Proof. exact (MK_COMB (@lem93624) (@lem93621 m n p)). Qed.
Lemma lem93627 (m : nat) (n : nat) : (term202 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem93593 m n) (@lem93592 m n)). Qed.
Lemma lem93628 (m : nat) (p : nat) : (term202 m p) = (Peano.le m p).
Proof. exact (@lem93627 m p). Qed.
Lemma lem93629 (n : nat) (m : nat) (p : nat) : (term169 n m p) = (term226 n m p).
Proof. exact (MK_COMB (@lem93625 m n p) (@lem93628 m p)). Qed.
Lemma lem93631 (n : nat) (p : nat) (m : nat) (h1 : term14 m) : (term226 n m p) = True.
Proof. exact (EQ_MP (@lem93601 n m p) (@lem93600 n p m h1)). Qed.
Lemma lem93632 (n : nat) (p : nat) (m : nat) (h1 : term14 m) : (term169 n m p) = True.
Proof. exact (TRANS (@lem93629 n m p) (@lem93631 n p m h1)). Qed.
Lemma lem93633 (n : nat) (p : nat) (m : nat) (h1 : term14 m) : True = (term169 n m p).
Proof. exact (SYM (@lem93632 n p m h1)). Qed.
Lemma lem93634 (n : nat) (p : nat) (m : nat) (h1 : term14 m) : term169 n m p.
Proof. exact (EQ_MP (@lem93633 n p m h1) (@lem0)). Qed.
Lemma lem93638 (m : nat) : (term5 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem93106 m) (@lem93105 m)). Qed.
Lemma lem93639 (m : nat) : (term193 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem93638 (S m)). Qed.
Lemma lem93641 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem93084 n (@lem93083 n)). Qed.
Lemma lem93642 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem93641 m). Qed.
Lemma lem93643 (m : nat) : (term193 m) = False.
Proof. exact (TRANS (@lem93639 m) (@lem93642 m)). Qed.
Lemma lem93644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93645 (m : nat) : (term197 m) = (imp False).
Proof. exact (MK_COMB (@lem93644) (@lem93643 m)). Qed.
Lemma lem93646 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem93647 (m : nat) (p : nat) : (term215 m p) = (term231 m p).
Proof. exact (MK_COMB (@lem93645 m) (@lem93646 m p)). Qed.
Lemma lem93649 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem93650 (m : nat) (p : nat) : (term231 m p) = True.
Proof. exact (@lem93649 (Peano.le m p)). Qed.
Lemma lem93651 (m : nat) (p : nat) : (term215 m p) = True.
Proof. exact (TRANS (@lem93647 m p) (@lem93650 m p)). Qed.
Lemma lem93652 (m : nat) (p : nat) : True = (term215 m p).
Proof. exact (SYM (@lem93651 m p)). Qed.
Lemma lem93653 (m : nat) (p : nat) : term215 m p.
Proof. exact (EQ_MP (@lem93652 m p) (@lem0)). Qed.
Lemma lem93659 (m : nat) : (term5 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem93106 m) (@lem93105 m)). Qed.
Lemma lem93660 (n : nat) : (term193 n) = ((S n) = (NUMERAL 0)).
Proof. exact (@lem93659 (S n)). Qed.
Lemma lem93662 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem93084 n (@lem93083 n)). Qed.
Lemma lem93663 (n : nat) : (term193 n) = False.
Proof. exact (TRANS (@lem93660 n) (@lem93662 n)). Qed.
Lemma lem93664 (m : nat) (n : nat) : (term217 m n) = (term217 m n).
Proof. exact (eq_refl (term217 m n)). Qed.
Lemma lem93665 (m : nat) (n : nat) : (term219 m n) = (term232 m n).
Proof. exact (MK_COMB (@lem93664 m n) (@lem93663 n)). Qed.
Lemma lem93667 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem93668 (m : nat) (n : nat) : (term232 m n) = False.
Proof. exact (@lem93667 (Peano.le m n)). Qed.
Lemma lem93669 (m : nat) (n : nat) : (term219 m n) = False.
Proof. exact (TRANS (@lem93665 m n) (@lem93668 m n)). Qed.
Lemma lem93670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93671 (m : nat) (n : nat) : (term221 m n) = (imp False).
Proof. exact (MK_COMB (@lem93670) (@lem93669 m n)). Qed.
Lemma lem93673 (m : nat) : (term5 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem93106 m) (@lem93105 m)). Qed.
Lemma lem93674 (m : nat) : (term193 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem93673 (S m)). Qed.
Lemma lem93676 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem93084 n (@lem93083 n)). Qed.
Lemma lem93677 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem93676 m). Qed.
Lemma lem93678 (m : nat) : (term193 m) = False.
Proof. exact (TRANS (@lem93674 m) (@lem93677 m)). Qed.
Lemma lem93679 (n : nat) (m : nat) : (term222 n m) = (False -> False).
Proof. exact (MK_COMB (@lem93671 m n) (@lem93678 m)). Qed.
Lemma lem93681 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem93682 : (False -> False) = True.
Proof. exact (@lem93681 False). Qed.
Lemma lem93683 (n : nat) (m : nat) : (term222 n m) = True.
Proof. exact (TRANS (@lem93679 n m) (@lem93682)). Qed.
Lemma lem93684 (n : nat) (m : nat) : True = (term222 n m).
Proof. exact (SYM (@lem93683 n m)). Qed.
Lemma lem93685 (n : nat) (m : nat) : term222 n m.
Proof. exact (EQ_MP (@lem93684 n m) (@lem0)). Qed.
Lemma lem93686 (n : nat) (m : nat) : term161 n m.
Proof. exact (EQ_MP (@lem93583 n m) (@lem93685 n m)). Qed.
Lemma lem93687 (m : nat) (p : nat) : term144 m p.
Proof. exact (EQ_MP (@lem93540 m p) (@lem93653 m p)). Qed.
Lemma lem93688 (n : nat) (p : nat) (m : nat) (h1 : term14 m) : term171 n m p.
Proof. exact (fun h0 : term165 n m p => @lem93634 n p m h1). Qed.
Lemma lem93693 (n : nat) (m : nat) (h1 : term14 m) : term175 n m.
Proof. exact (fun p : nat => @lem93688 n p m h1). Qed.
Lemma lem93694 (n : nat) (m : nat) (h1 : term14 m) : term177 n m.
Proof. exact (conj (@lem93686 n m) (@lem93693 n m h1)). Qed.
Lemma lem93695 (n : nat) (m : nat) (h1 : term14 m) : term119 n m.
Proof. exact (@lem93286 n m (@lem93694 n m h1)). Qed.
Lemma lem93696 (m : nat) (p : nat) : term146 m p.
Proof. exact (fun h0 : term140 m p => @lem93687 m p). Qed.
Lemma lem93701 (m : nat) : term150 m.
Proof. exact (fun p : nat => @lem93696 m p). Qed.
Lemma lem93702 (m : nat) : term152 m.
Proof. exact (conj (@lem93497 m) (@lem93701 m)). Qed.
Lemma lem93703 (m : nat) : term111 m.
Proof. exact (@lem93258 m (@lem93702 m)). Qed.
Lemma lem93704 (n : nat) (m : nat) (h1 : term14 m) : term121 n m.
Proof. exact (fun h0 : term115 n m => @lem93695 n m h1). Qed.
Lemma lem93709 (m : nat) (h1 : term14 m) : term125 m.
Proof. exact (fun n : nat => @lem93704 n m h1). Qed.
Lemma lem93710 (m : nat) (h1 : term14 m) : term127 m.
Proof. exact (conj (@lem93703 m) (@lem93709 m h1)). Qed.
Lemma lem93711 (m : nat) (h1 : term14 m) : term18 m.
Proof. exact (@lem93234 m (@lem93710 m h1)). Qed.
Lemma lem93712 (n : nat) (p : nat) : term96 n p.
Proof. exact (fun h0 : term90 n p => @lem93455 n p). Qed.
Lemma lem93717 (n : nat) : term100 n.
Proof. exact (fun p : nat => @lem93712 n p). Qed.
Lemma lem93718 (n : nat) : term102 n.
Proof. exact (conj (@lem93408 n) (@lem93717 n)). Qed.
Lemma lem93719 (n : nat) : term44 n.
Proof. exact (@lem93206 n (@lem93718 n)). Qed.
Lemma lem93720 (p : nat) : term71 p.
Proof. exact (fun h0 : term65 p => @lem93365 p). Qed.
Lemma lem93725 : term75.
Proof. exact (fun p : nat => @lem93720 p). Qed.
Lemma lem93726 : term77.
Proof. exact (conj (@lem93323) (@lem93725)). Qed.
Lemma lem93727 : term36.
Proof. exact (@lem93178 (@lem93726)). Qed.
Lemma lem93728 (n : nat) : term46 n.
Proof. exact (fun h0 : term40 n => @lem93719 n). Qed.
Lemma lem93733 : term50.
Proof. exact (fun n : nat => @lem93728 n). Qed.
Lemma lem93734 : term52.
Proof. exact (conj (@lem93727) (@lem93733)). Qed.
Lemma lem93735 : term10.
Proof. exact (@lem93154 (@lem93734)). Qed.
Lemma lem93736 (m : nat) : term20 m.
Proof. exact (fun h0 : term14 m => @lem93711 m h0). Qed.
Lemma lem93741 : term24.
Proof. exact (fun m : nat => @lem93736 m). Qed.
Lemma lem93742 : term26.
Proof. exact (conj (@lem93735) (@lem93741)). Qed.
Lemma lem93743 : term31.
Proof. exact (@lem93130 (@lem93742)). Qed.
