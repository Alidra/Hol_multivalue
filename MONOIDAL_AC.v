Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONOIDAL_AC_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Lemma lem5712813 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem5712814 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem5712823 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem5712814 A op) (@lem5712813 A op)). Qed.
Lemma lem5712824 {_119721 : Type'} (op : type1400 _119721) : (@monoidal _119721 op) = (term1 _119721 op).
Proof. exact (@lem5712823 _119721 op). Qed.
Lemma lem5712859 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5712860 {_119721 : Type'} (op : type1400 _119721) : (term2 _119721 op) = (term3 _119721 op).
Proof. exact (MK_COMB (@lem5712859) (@lem5712824 _119721 op)). Qed.
Lemma lem5712919 {_119721 : Type'} (op : type1400 _119721) : (term4 _119721 op) = (term4 _119721 op).
Proof. exact (eq_refl (term4 _119721 op)). Qed.
Lemma lem5712920 {_119721 : Type'} (op : type1400 _119721) : (term5 _119721 op) = (term6 _119721 op).
Proof. exact (MK_COMB (@lem5712860 _119721 op) (@lem5712919 _119721 op)). Qed.
Lemma lem5712923 {_119721 : Type'} : (term7 _119721) = (term8 _119721).
Proof. exact (fun_ext (fun op : type1400 _119721 => @lem5712920 _119721 op)). Qed.
Lemma lem5712924 {_119721 : Type'} : (@all (_119721 -> _119721 -> _119721)) = (@all (_119721 -> _119721 -> _119721)).
Proof. exact (eq_refl (@all (_119721 -> _119721 -> _119721))). Qed.
Lemma lem5712925 {_119721 : Type'} : (term9 _119721) = (term10 _119721).
Proof. exact (MK_COMB (@lem5712924 _119721) (@lem5712923 _119721)). Qed.
Lemma lem5712930 {_119721 : Type'} : (term10 _119721) = (term9 _119721).
Proof. exact (SYM (@lem5712925 _119721)). Qed.
Lemma lem5712932 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5712933 {_119721 : Type'} : (term10 _119721) = (term12 _119721).
Proof. exact (@lem5712932 (term10 _119721)). Qed.
Lemma lem5712934 {_119721 : Type'} : (term12 _119721) = (term10 _119721).
Proof. exact (SYM (@lem5712933 _119721)). Qed.
Lemma lem5712935 {_119721 : Type'} (h1 : term13 _119721) : term13 _119721.
Proof. exact (h1). Qed.
Lemma lem5712938 {_119721 : Type'} (h1 : term12 _119721) : term12 _119721.
Proof. exact (h1). Qed.
Lemma lem5712939 {_119721 : Type'} : term14 _119721.
Proof. exact (fun h0 : term12 _119721 => @lem5712938 _119721 h0). Qed.
Lemma lem5712940 {_119721 : Type'} (h1 : term14 _119721) : term14 _119721.
Proof. exact (h1). Qed.
Lemma lem5712941 {_119721 : Type'} (h1 : term12 _119721) : term12 _119721.
Proof. exact (h1). Qed.
Lemma lem5712942 {_119721 : Type'} (h1 : term12 _119721) (h2 : term14 _119721) : term12 _119721.
Proof. exact (@lem5712940 _119721 h2 (@lem5712941 _119721 h1)). Qed.
Lemma lem5712943 {_119721 : Type'} (h1 : term12 _119721) : term15 _119721.
Proof. exact (fun h0 : term14 _119721 => @lem5712942 _119721 h1 h0). Qed.
Lemma lem5712944 {_119721 : Type'} (h1 : term14 _119721) : term14 _119721.
Proof. exact (h1). Qed.
Lemma lem5712945 {_119721 : Type'} (h1 : term12 _119721) (h2 : term14 _119721) : term12 _119721.
Proof. exact (@lem5712943 _119721 h1 (@lem5712944 _119721 h2)). Qed.
Lemma lem5712946 {_119721 : Type'} (h1 : term14 _119721) : term14 _119721.
Proof. exact (fun h0 : term12 _119721 => @lem5712945 _119721 h0 h1). Qed.
Lemma lem5712947 {_119721 : Type'} : term16 _119721.
Proof. exact (fun h0 : term14 _119721 => @lem5712946 _119721 h0). Qed.
Lemma lem5712950 {_119721 : Type'} : term14 _119721.
Proof. exact (@lem5712947 _119721 (@lem5712939 _119721)). Qed.
Lemma lem5712951 {_119721 : Type'} : term14 _119721.
Proof. exact (@lem5712950 _119721). Qed.
Lemma lem5712953 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5712954 {_119721 : Type'} : (term12 _119721) = (term17 _119721).
Proof. exact (@lem5712953 (term13 _119721)). Qed.
Lemma lem5712956 (t : Prop) : (term18 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5712957 {_119721 : Type'} : (term17 _119721) = (term10 _119721).
Proof. exact (@lem5712956 (term10 _119721)). Qed.
Lemma lem5713044 {_119721 : Type'} : (term12 _119721) = (term10 _119721).
Proof. exact (TRANS (@lem5712954 _119721) (@lem5712957 _119721)). Qed.
Lemma lem5713045 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : ((term19 _119721 a op b c) = (term19 _119721 b op a c)) = ((term19 _119721 a op b c) = (term19 _119721 b op a c)).
Proof. exact (eq_refl ((term19 _119721 a op b c) = (term19 _119721 b op a c))). Qed.
Lemma lem5713046 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term20 _119721 b op a) = (term20 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713045 _119721 b op a c)). Qed.
Lemma lem5713047 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713048 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term21 _119721 b op a) = (term21 _119721 b op a).
Proof. exact (MK_COMB (@lem5713047 _119721) (@lem5713046 _119721 b op a)). Qed.
Lemma lem5713049 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term22 _119721 op a) = (term22 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713048 _119721 b op a)). Qed.
Lemma lem5713050 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713051 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term23 _119721 op a) = (term23 _119721 op a).
Proof. exact (MK_COMB (@lem5713050 _119721) (@lem5713049 _119721 op a)). Qed.
Lemma lem5713052 {_119721 : Type'} (op : type1400 _119721) : (term24 _119721 op) = (term24 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713051 _119721 op a)). Qed.
Lemma lem5713053 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713054 {_119721 : Type'} (op : type1400 _119721) : (term25 _119721 op) = (term25 _119721 op).
Proof. exact (MK_COMB (@lem5713053 _119721) (@lem5713052 _119721 op)). Qed.
Lemma lem5713055 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : ((term26 _119721 op a b c) = (term19 _119721 a op b c)) = ((term26 _119721 op a b c) = (term19 _119721 a op b c)).
Proof. exact (eq_refl ((term26 _119721 op a b c) = (term19 _119721 a op b c))). Qed.
Lemma lem5713056 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term27 _119721 a op b) = (term27 _119721 a op b).
Proof. exact (fun_ext (fun c : _119721 => @lem5713055 _119721 a op b c)). Qed.
Lemma lem5713057 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713058 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term28 _119721 a op b) = (term28 _119721 a op b).
Proof. exact (MK_COMB (@lem5713057 _119721) (@lem5713056 _119721 a op b)). Qed.
Lemma lem5713059 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term29 _119721 a op) = (term29 _119721 a op).
Proof. exact (fun_ext (fun b : _119721 => @lem5713058 _119721 a op b)). Qed.
Lemma lem5713060 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713061 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term30 _119721 a op) = (term30 _119721 a op).
Proof. exact (MK_COMB (@lem5713060 _119721) (@lem5713059 _119721 a op)). Qed.
Lemma lem5713062 {_119721 : Type'} (op : type1400 _119721) : (term31 _119721 op) = (term31 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713061 _119721 a op)). Qed.
Lemma lem5713063 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713064 {_119721 : Type'} (op : type1400 _119721) : (term32 _119721 op) = (term32 _119721 op).
Proof. exact (MK_COMB (@lem5713063 _119721) (@lem5713062 _119721 op)). Qed.
Lemma lem5713065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713066 {_119721 : Type'} (op : type1400 _119721) : (term33 _119721 op) = (term33 _119721 op).
Proof. exact (MK_COMB (@lem5713065) (@lem5713064 _119721 op)). Qed.
Lemma lem5713067 {_119721 : Type'} (op : type1400 _119721) : (term34 _119721 op) = (term34 _119721 op).
Proof. exact (MK_COMB (@lem5713066 _119721 op) (@lem5713054 _119721 op)). Qed.
Lemma lem5713068 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : ((op a b) = (op b a)) = ((op a b) = (op b a)).
Proof. exact (eq_refl ((op a b) = (op b a))). Qed.
Lemma lem5713069 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term35 _119721 op a) = (term35 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713068 _119721 op b a)). Qed.
Lemma lem5713070 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713071 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term36 _119721 op a) = (term36 _119721 op a).
Proof. exact (MK_COMB (@lem5713070 _119721) (@lem5713069 _119721 op a)). Qed.
Lemma lem5713072 {_119721 : Type'} (op : type1400 _119721) : (term37 _119721 op) = (term37 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713071 _119721 op a)). Qed.
Lemma lem5713073 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713074 {_119721 : Type'} (op : type1400 _119721) : (term38 _119721 op) = (term38 _119721 op).
Proof. exact (MK_COMB (@lem5713073 _119721) (@lem5713072 _119721 op)). Qed.
Lemma lem5713075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713076 {_119721 : Type'} (op : type1400 _119721) : (term39 _119721 op) = (term39 _119721 op).
Proof. exact (MK_COMB (@lem5713075) (@lem5713074 _119721 op)). Qed.
Lemma lem5713077 {_119721 : Type'} (op : type1400 _119721) : (term40 _119721 op) = (term40 _119721 op).
Proof. exact (MK_COMB (@lem5713076 _119721 op) (@lem5713067 _119721 op)). Qed.
Lemma lem5713078 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term41 _119721 a op) = a) = ((term41 _119721 a op) = a).
Proof. exact (eq_refl ((term41 _119721 a op) = a)). Qed.
Lemma lem5713079 {_119721 : Type'} (op : type1400 _119721) : (term42 _119721 op) = (term42 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713078 _119721 op a)). Qed.
Lemma lem5713080 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713081 {_119721 : Type'} (op : type1400 _119721) : (term43 _119721 op) = (term43 _119721 op).
Proof. exact (MK_COMB (@lem5713080 _119721) (@lem5713079 _119721 op)). Qed.
Lemma lem5713082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713083 {_119721 : Type'} (op : type1400 _119721) : (term44 _119721 op) = (term44 _119721 op).
Proof. exact (MK_COMB (@lem5713082) (@lem5713081 _119721 op)). Qed.
Lemma lem5713084 {_119721 : Type'} (op : type1400 _119721) : (term45 _119721 op) = (term45 _119721 op).
Proof. exact (MK_COMB (@lem5713083 _119721 op) (@lem5713077 _119721 op)). Qed.
Lemma lem5713085 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term46 _119721 op a) = a) = ((term46 _119721 op a) = a).
Proof. exact (eq_refl ((term46 _119721 op a) = a)). Qed.
Lemma lem5713086 {_119721 : Type'} (op : type1400 _119721) : (term47 _119721 op) = (term47 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713085 _119721 op a)). Qed.
Lemma lem5713087 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713088 {_119721 : Type'} (op : type1400 _119721) : (term48 _119721 op) = (term48 _119721 op).
Proof. exact (MK_COMB (@lem5713087 _119721) (@lem5713086 _119721 op)). Qed.
Lemma lem5713089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713090 {_119721 : Type'} (op : type1400 _119721) : (term49 _119721 op) = (term49 _119721 op).
Proof. exact (MK_COMB (@lem5713089) (@lem5713088 _119721 op)). Qed.
Lemma lem5713091 {_119721 : Type'} (op : type1400 _119721) : (term4 _119721 op) = (term4 _119721 op).
Proof. exact (MK_COMB (@lem5713090 _119721 op) (@lem5713084 _119721 op)). Qed.
Lemma lem5713092 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : ((term46 _119721 op x) = x) = ((term46 _119721 op x) = x).
Proof. exact (eq_refl ((term46 _119721 op x) = x)). Qed.
Lemma lem5713093 {_119721 : Type'} (op : type1400 _119721) : (term47 _119721 op) = (term47 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713092 _119721 op x)). Qed.
Lemma lem5713094 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713095 {_119721 : Type'} (op : type1400 _119721) : (term48 _119721 op) = (term48 _119721 op).
Proof. exact (MK_COMB (@lem5713094 _119721) (@lem5713093 _119721 op)). Qed.
Lemma lem5713096 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : ((term19 _119721 x op y z) = (term26 _119721 op x y z)) = ((term19 _119721 x op y z) = (term26 _119721 op x y z)).
Proof. exact (eq_refl ((term19 _119721 x op y z) = (term26 _119721 op x y z))). Qed.
Lemma lem5713097 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term50 _119721 op x y) = (term50 _119721 op x y).
Proof. exact (fun_ext (fun z : _119721 => @lem5713096 _119721 op x y z)). Qed.
Lemma lem5713098 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713099 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term51 _119721 op x y) = (term51 _119721 op x y).
Proof. exact (MK_COMB (@lem5713098 _119721) (@lem5713097 _119721 op x y)). Qed.
Lemma lem5713100 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term52 _119721 op x) = (term52 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5713099 _119721 op x y)). Qed.
Lemma lem5713101 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713102 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term53 _119721 op x) = (term53 _119721 op x).
Proof. exact (MK_COMB (@lem5713101 _119721) (@lem5713100 _119721 op x)). Qed.
Lemma lem5713103 {_119721 : Type'} (op : type1400 _119721) : (term54 _119721 op) = (term54 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713102 _119721 op x)). Qed.
Lemma lem5713104 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713105 {_119721 : Type'} (op : type1400 _119721) : (term55 _119721 op) = (term55 _119721 op).
Proof. exact (MK_COMB (@lem5713104 _119721) (@lem5713103 _119721 op)). Qed.
Lemma lem5713106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713107 {_119721 : Type'} (op : type1400 _119721) : (term56 _119721 op) = (term56 _119721 op).
Proof. exact (MK_COMB (@lem5713106) (@lem5713105 _119721 op)). Qed.
Lemma lem5713108 {_119721 : Type'} (op : type1400 _119721) : (term57 _119721 op) = (term57 _119721 op).
Proof. exact (MK_COMB (@lem5713107 _119721 op) (@lem5713095 _119721 op)). Qed.
Lemma lem5713109 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem5713110 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term35 _119721 op x) = (term35 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5713109 _119721 op y x)). Qed.
Lemma lem5713111 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713112 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term36 _119721 op x) = (term36 _119721 op x).
Proof. exact (MK_COMB (@lem5713111 _119721) (@lem5713110 _119721 op x)). Qed.
Lemma lem5713113 {_119721 : Type'} (op : type1400 _119721) : (term37 _119721 op) = (term37 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713112 _119721 op x)). Qed.
Lemma lem5713114 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713115 {_119721 : Type'} (op : type1400 _119721) : (term38 _119721 op) = (term38 _119721 op).
Proof. exact (MK_COMB (@lem5713114 _119721) (@lem5713113 _119721 op)). Qed.
Lemma lem5713116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713117 {_119721 : Type'} (op : type1400 _119721) : (term39 _119721 op) = (term39 _119721 op).
Proof. exact (MK_COMB (@lem5713116) (@lem5713115 _119721 op)). Qed.
Lemma lem5713118 {_119721 : Type'} (op : type1400 _119721) : (term1 _119721 op) = (term1 _119721 op).
Proof. exact (MK_COMB (@lem5713117 _119721 op) (@lem5713108 _119721 op)). Qed.
Lemma lem5713119 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5713120 {_119721 : Type'} (op : type1400 _119721) : (term3 _119721 op) = (term3 _119721 op).
Proof. exact (MK_COMB (@lem5713119) (@lem5713118 _119721 op)). Qed.
Lemma lem5713121 {_119721 : Type'} (op : type1400 _119721) : (term6 _119721 op) = (term6 _119721 op).
Proof. exact (MK_COMB (@lem5713120 _119721 op) (@lem5713091 _119721 op)). Qed.
Lemma lem5713122 {_119721 : Type'} : (term8 _119721) = (term8 _119721).
Proof. exact (fun_ext (fun op : type1400 _119721 => @lem5713121 _119721 op)). Qed.
Lemma lem5713123 {_119721 : Type'} : (@all (_119721 -> _119721 -> _119721)) = (@all (_119721 -> _119721 -> _119721)).
Proof. exact (eq_refl (@all (_119721 -> _119721 -> _119721))). Qed.
Lemma lem5713124 {_119721 : Type'} : (term10 _119721) = (term10 _119721).
Proof. exact (MK_COMB (@lem5713123 _119721) (@lem5713122 _119721)). Qed.
Lemma lem5713243 {_119721 : Type'} : (term12 _119721) = (term10 _119721).
Proof. exact (TRANS (@lem5713044 _119721) (@lem5713124 _119721)). Qed.
Lemma lem5713244 {_119721 : Type'} : (term10 _119721) = (term12 _119721).
Proof. exact (SYM (@lem5713243 _119721)). Qed.
Lemma lem5713245 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term1 _119721 op.
Proof. exact (h1). Qed.
Lemma lem5713247 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5713248 {_119721 : Type'} (op : type1400 _119721) : (term4 _119721 op) = (term58 _119721 op).
Proof. exact (@lem5713247 (term4 _119721 op)). Qed.
Lemma lem5713249 {_119721 : Type'} (op : type1400 _119721) : (term58 _119721 op) = (term4 _119721 op).
Proof. exact (SYM (@lem5713248 _119721 op)). Qed.
Lemma lem5713250 {_119721 : Type'} (op : type1400 _119721) (h1 : term59 _119721 op) : term59 _119721 op.
Proof. exact (h1). Qed.
Lemma lem5713251 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : ((op x y) = (op y x)) = ((op x y) = (op y x)).
Proof. exact (eq_refl ((op x y) = (op y x))). Qed.
Lemma lem5713252 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term35 _119721 op x) = (term35 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5713251 _119721 op y x)). Qed.
Lemma lem5713253 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713254 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term36 _119721 op x) = (term36 _119721 op x).
Proof. exact (MK_COMB (@lem5713253 _119721) (@lem5713252 _119721 op x)). Qed.
Lemma lem5713255 {_119721 : Type'} (op : type1400 _119721) : (term37 _119721 op) = (term37 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713254 _119721 op x)). Qed.
Lemma lem5713256 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713257 {_119721 : Type'} (op : type1400 _119721) : (term38 _119721 op) = (term38 _119721 op).
Proof. exact (MK_COMB (@lem5713256 _119721) (@lem5713255 _119721 op)). Qed.
Lemma lem5713258 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : ((term19 _119721 x op y z) = (term26 _119721 op x y z)) = ((term19 _119721 x op y z) = (term26 _119721 op x y z)).
Proof. exact (eq_refl ((term19 _119721 x op y z) = (term26 _119721 op x y z))). Qed.
Lemma lem5713259 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term50 _119721 op x y) = (term50 _119721 op x y).
Proof. exact (fun_ext (fun z : _119721 => @lem5713258 _119721 op x y z)). Qed.
Lemma lem5713260 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713261 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term51 _119721 op x y) = (term51 _119721 op x y).
Proof. exact (MK_COMB (@lem5713260 _119721) (@lem5713259 _119721 op x y)). Qed.
Lemma lem5713262 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term52 _119721 op x) = (term52 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5713261 _119721 op x y)). Qed.
Lemma lem5713263 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713264 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term53 _119721 op x) = (term53 _119721 op x).
Proof. exact (MK_COMB (@lem5713263 _119721) (@lem5713262 _119721 op x)). Qed.
Lemma lem5713265 {_119721 : Type'} (op : type1400 _119721) : (term54 _119721 op) = (term54 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713264 _119721 op x)). Qed.
Lemma lem5713266 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713267 {_119721 : Type'} (op : type1400 _119721) : (term55 _119721 op) = (term55 _119721 op).
Proof. exact (MK_COMB (@lem5713266 _119721) (@lem5713265 _119721 op)). Qed.
Lemma lem5713268 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : ((term46 _119721 op x) = x) = ((term46 _119721 op x) = x).
Proof. exact (eq_refl ((term46 _119721 op x) = x)). Qed.
Lemma lem5713269 {_119721 : Type'} (op : type1400 _119721) : (term47 _119721 op) = (term47 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713268 _119721 op x)). Qed.
Lemma lem5713270 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713271 {_119721 : Type'} (op : type1400 _119721) : (term48 _119721 op) = (term48 _119721 op).
Proof. exact (MK_COMB (@lem5713270 _119721) (@lem5713269 _119721 op)). Qed.
Lemma lem5713272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713273 {_119721 : Type'} (op : type1400 _119721) : (term56 _119721 op) = (term56 _119721 op).
Proof. exact (MK_COMB (@lem5713272) (@lem5713267 _119721 op)). Qed.
Lemma lem5713274 {_119721 : Type'} (op : type1400 _119721) : (term57 _119721 op) = (term57 _119721 op).
Proof. exact (MK_COMB (@lem5713273 _119721 op) (@lem5713271 _119721 op)). Qed.
Lemma lem5713275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713276 {_119721 : Type'} (op : type1400 _119721) : (term39 _119721 op) = (term39 _119721 op).
Proof. exact (MK_COMB (@lem5713275) (@lem5713257 _119721 op)). Qed.
Lemma lem5713305 {_119721 : Type'} (op : type1400 _119721) : (term1 _119721 op) = (term1 _119721 op).
Proof. exact (MK_COMB (@lem5713276 _119721 op) (@lem5713274 _119721 op)). Qed.
Lemma lem5713306 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term1 _119721 op.
Proof. exact (EQ_MP (@lem5713305 _119721 op) (@lem5713245 _119721 op h1)). Qed.
Lemma lem5713308 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713309 {_119721 : Type'} (op : type1400 _119721) : (term62 _119721 op) = (term63 _119721 op).
Proof. exact (@lem5713308 _119721 (term47 _119721 op)). Qed.
Lemma lem5713310 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term64 _119721 op a) = ((term46 _119721 op a) = a).
Proof. exact (eq_refl (term64 _119721 op a)). Qed.
Lemma lem5713311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713313 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term65 _119721 op a) = (term66 _119721 op a).
Proof. exact (MK_COMB (@lem5713311) (@lem5713310 _119721 op a)). Qed.
Lemma lem5713314 {_119721 : Type'} (op : type1400 _119721) : (term67 _119721 op) = (term68 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713313 _119721 op a)). Qed.
Lemma lem5713315 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713316 {_119721 : Type'} (op : type1400 _119721) : (term63 _119721 op) = (term69 _119721 op).
Proof. exact (MK_COMB (@lem5713315 _119721) (@lem5713314 _119721 op)). Qed.
Lemma lem5713317 {_119721 : Type'} (op : type1400 _119721) : (term62 _119721 op) = (term69 _119721 op).
Proof. exact (TRANS (@lem5713309 _119721 op) (@lem5713316 _119721 op)). Qed.
Lemma lem5713319 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713320 {_119721 : Type'} (op : type1400 _119721) : (term70 _119721 op) = (term71 _119721 op).
Proof. exact (@lem5713319 _119721 (term42 _119721 op)). Qed.
Lemma lem5713321 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term72 _119721 op a) = ((term41 _119721 a op) = a).
Proof. exact (eq_refl (term72 _119721 op a)). Qed.
Lemma lem5713322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713324 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term73 _119721 op a) = (term74 _119721 op a).
Proof. exact (MK_COMB (@lem5713322) (@lem5713321 _119721 op a)). Qed.
Lemma lem5713325 {_119721 : Type'} (op : type1400 _119721) : (term75 _119721 op) = (term76 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713324 _119721 op a)). Qed.
Lemma lem5713326 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713327 {_119721 : Type'} (op : type1400 _119721) : (term71 _119721 op) = (term77 _119721 op).
Proof. exact (MK_COMB (@lem5713326 _119721) (@lem5713325 _119721 op)). Qed.
Lemma lem5713328 {_119721 : Type'} (op : type1400 _119721) : (term70 _119721 op) = (term77 _119721 op).
Proof. exact (TRANS (@lem5713320 _119721 op) (@lem5713327 _119721 op)). Qed.
Lemma lem5713330 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713331 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term78 _119721 op a) = (term79 _119721 op a).
Proof. exact (@lem5713330 _119721 (term35 _119721 op a)). Qed.
Lemma lem5713332 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term80 _119721 op a b) = ((op a b) = (op b a)).
Proof. exact (eq_refl (term80 _119721 op a b)). Qed.
Lemma lem5713333 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713335 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term81 _119721 op a b) = (term82 _119721 op b a).
Proof. exact (MK_COMB (@lem5713333) (@lem5713332 _119721 op b a)). Qed.
Lemma lem5713336 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term83 _119721 op a) = (term84 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713335 _119721 op b a)). Qed.
Lemma lem5713337 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713338 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term79 _119721 op a) = (term85 _119721 op a).
Proof. exact (MK_COMB (@lem5713337 _119721) (@lem5713336 _119721 op a)). Qed.
Lemma lem5713339 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term78 _119721 op a) = (term85 _119721 op a).
Proof. exact (TRANS (@lem5713331 _119721 op a) (@lem5713338 _119721 op a)). Qed.
Lemma lem5713340 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713341 {_119721 : Type'} (op : type1400 _119721) : (term86 _119721 op) = (term87 _119721 op).
Proof. exact (@lem5713340 _119721 (term37 _119721 op)). Qed.
Lemma lem5713342 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term88 _119721 op a) = (term36 _119721 op a).
Proof. exact (eq_refl (term88 _119721 op a)). Qed.
Lemma lem5713343 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713344 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term89 _119721 op a) = (term78 _119721 op a).
Proof. exact (MK_COMB (@lem5713343) (@lem5713342 _119721 op a)). Qed.
Lemma lem5713345 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term89 _119721 op a) = (term85 _119721 op a).
Proof. exact (TRANS (@lem5713344 _119721 op a) (@lem5713339 _119721 op a)). Qed.
Lemma lem5713346 {_119721 : Type'} (op : type1400 _119721) : (term90 _119721 op) = (term91 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713345 _119721 op a)). Qed.
Lemma lem5713347 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713348 {_119721 : Type'} (op : type1400 _119721) : (term87 _119721 op) = (term92 _119721 op).
Proof. exact (MK_COMB (@lem5713347 _119721) (@lem5713346 _119721 op)). Qed.
Lemma lem5713349 {_119721 : Type'} (op : type1400 _119721) : (term86 _119721 op) = (term92 _119721 op).
Proof. exact (TRANS (@lem5713341 _119721 op) (@lem5713348 _119721 op)). Qed.
Lemma lem5713351 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713352 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term93 _119721 a op b) = (term94 _119721 a op b).
Proof. exact (@lem5713351 _119721 (term27 _119721 a op b)). Qed.
Lemma lem5713353 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term95 _119721 a op b c) = ((term26 _119721 op a b c) = (term19 _119721 a op b c)).
Proof. exact (eq_refl (term95 _119721 a op b c)). Qed.
Lemma lem5713354 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713356 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term96 _119721 a op b c) = (term97 _119721 a op b c).
Proof. exact (MK_COMB (@lem5713354) (@lem5713353 _119721 a op b c)). Qed.
Lemma lem5713357 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term98 _119721 a op b) = (term99 _119721 a op b).
Proof. exact (fun_ext (fun c : _119721 => @lem5713356 _119721 a op b c)). Qed.
Lemma lem5713358 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713359 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term94 _119721 a op b) = (term100 _119721 a op b).
Proof. exact (MK_COMB (@lem5713358 _119721) (@lem5713357 _119721 a op b)). Qed.
Lemma lem5713360 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term93 _119721 a op b) = (term100 _119721 a op b).
Proof. exact (TRANS (@lem5713352 _119721 a op b) (@lem5713359 _119721 a op b)). Qed.
Lemma lem5713361 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713362 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term101 _119721 a op) = (term102 _119721 a op).
Proof. exact (@lem5713361 _119721 (term29 _119721 a op)). Qed.
Lemma lem5713363 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term103 _119721 a op b) = (term28 _119721 a op b).
Proof. exact (eq_refl (term103 _119721 a op b)). Qed.
Lemma lem5713364 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713365 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term104 _119721 a op b) = (term93 _119721 a op b).
Proof. exact (MK_COMB (@lem5713364) (@lem5713363 _119721 a op b)). Qed.
Lemma lem5713366 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term104 _119721 a op b) = (term100 _119721 a op b).
Proof. exact (TRANS (@lem5713365 _119721 a op b) (@lem5713360 _119721 a op b)). Qed.
Lemma lem5713367 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term105 _119721 a op) = (term106 _119721 a op).
Proof. exact (fun_ext (fun b : _119721 => @lem5713366 _119721 a op b)). Qed.
Lemma lem5713368 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713369 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term102 _119721 a op) = (term107 _119721 a op).
Proof. exact (MK_COMB (@lem5713368 _119721) (@lem5713367 _119721 a op)). Qed.
Lemma lem5713370 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term101 _119721 a op) = (term107 _119721 a op).
Proof. exact (TRANS (@lem5713362 _119721 a op) (@lem5713369 _119721 a op)). Qed.
Lemma lem5713371 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713372 {_119721 : Type'} (op : type1400 _119721) : (term108 _119721 op) = (term109 _119721 op).
Proof. exact (@lem5713371 _119721 (term31 _119721 op)). Qed.
Lemma lem5713373 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term110 _119721 op a) = (term30 _119721 a op).
Proof. exact (eq_refl (term110 _119721 op a)). Qed.
Lemma lem5713374 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713375 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term111 _119721 op a) = (term101 _119721 a op).
Proof. exact (MK_COMB (@lem5713374) (@lem5713373 _119721 a op)). Qed.
Lemma lem5713376 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term111 _119721 op a) = (term107 _119721 a op).
Proof. exact (TRANS (@lem5713375 _119721 a op) (@lem5713370 _119721 a op)). Qed.
Lemma lem5713377 {_119721 : Type'} (op : type1400 _119721) : (term112 _119721 op) = (term113 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713376 _119721 a op)). Qed.
Lemma lem5713378 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713379 {_119721 : Type'} (op : type1400 _119721) : (term109 _119721 op) = (term114 _119721 op).
Proof. exact (MK_COMB (@lem5713378 _119721) (@lem5713377 _119721 op)). Qed.
Lemma lem5713380 {_119721 : Type'} (op : type1400 _119721) : (term108 _119721 op) = (term114 _119721 op).
Proof. exact (TRANS (@lem5713372 _119721 op) (@lem5713379 _119721 op)). Qed.
Lemma lem5713382 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713383 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term115 _119721 b op a) = (term116 _119721 b op a).
Proof. exact (@lem5713382 _119721 (term20 _119721 b op a)). Qed.
Lemma lem5713384 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term117 _119721 b op a c) = ((term19 _119721 a op b c) = (term19 _119721 b op a c)).
Proof. exact (eq_refl (term117 _119721 b op a c)). Qed.
Lemma lem5713385 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713387 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term118 _119721 b op a c) = (term119 _119721 b op a c).
Proof. exact (MK_COMB (@lem5713385) (@lem5713384 _119721 b op a c)). Qed.
Lemma lem5713388 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term120 _119721 b op a) = (term121 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713387 _119721 b op a c)). Qed.
Lemma lem5713389 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713390 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term116 _119721 b op a) = (term122 _119721 b op a).
Proof. exact (MK_COMB (@lem5713389 _119721) (@lem5713388 _119721 b op a)). Qed.
Lemma lem5713391 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term115 _119721 b op a) = (term122 _119721 b op a).
Proof. exact (TRANS (@lem5713383 _119721 b op a) (@lem5713390 _119721 b op a)). Qed.
Lemma lem5713392 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713393 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term123 _119721 op a) = (term124 _119721 op a).
Proof. exact (@lem5713392 _119721 (term22 _119721 op a)). Qed.
Lemma lem5713394 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term125 _119721 op a b) = (term21 _119721 b op a).
Proof. exact (eq_refl (term125 _119721 op a b)). Qed.
Lemma lem5713395 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713396 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term126 _119721 op a b) = (term115 _119721 b op a).
Proof. exact (MK_COMB (@lem5713395) (@lem5713394 _119721 b op a)). Qed.
Lemma lem5713397 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term126 _119721 op a b) = (term122 _119721 b op a).
Proof. exact (TRANS (@lem5713396 _119721 b op a) (@lem5713391 _119721 b op a)). Qed.
Lemma lem5713398 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term127 _119721 op a) = (term128 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713397 _119721 b op a)). Qed.
Lemma lem5713399 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713400 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term124 _119721 op a) = (term129 _119721 op a).
Proof. exact (MK_COMB (@lem5713399 _119721) (@lem5713398 _119721 op a)). Qed.
Lemma lem5713401 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term123 _119721 op a) = (term129 _119721 op a).
Proof. exact (TRANS (@lem5713393 _119721 op a) (@lem5713400 _119721 op a)). Qed.
Lemma lem5713402 {_119721 : Type'} (P : _119721 -> Prop) : (term60 _119721 P) = (term61 _119721 P).
Proof. exact (@lem18392 _119721 P). Qed.
Lemma lem5713403 {_119721 : Type'} (op : type1400 _119721) : (term130 _119721 op) = (term131 _119721 op).
Proof. exact (@lem5713402 _119721 (term24 _119721 op)). Qed.
Lemma lem5713404 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term132 _119721 op a) = (term23 _119721 op a).
Proof. exact (eq_refl (term132 _119721 op a)). Qed.
Lemma lem5713405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713406 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term133 _119721 op a) = (term123 _119721 op a).
Proof. exact (MK_COMB (@lem5713405) (@lem5713404 _119721 op a)). Qed.
Lemma lem5713407 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term133 _119721 op a) = (term129 _119721 op a).
Proof. exact (TRANS (@lem5713406 _119721 op a) (@lem5713401 _119721 op a)). Qed.
Lemma lem5713408 {_119721 : Type'} (op : type1400 _119721) : (term134 _119721 op) = (term135 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713407 _119721 op a)). Qed.
Lemma lem5713409 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713410 {_119721 : Type'} (op : type1400 _119721) : (term131 _119721 op) = (term136 _119721 op).
Proof. exact (MK_COMB (@lem5713409 _119721) (@lem5713408 _119721 op)). Qed.
Lemma lem5713411 {_119721 : Type'} (op : type1400 _119721) : (term130 _119721 op) = (term136 _119721 op).
Proof. exact (TRANS (@lem5713403 _119721 op) (@lem5713410 _119721 op)). Qed.
Lemma lem5713412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713413 {_119721 : Type'} (op : type1400 _119721) : (term137 _119721 op) = (term138 _119721 op).
Proof. exact (MK_COMB (@lem5713412) (@lem5713380 _119721 op)). Qed.
Lemma lem5713414 {_119721 : Type'} (op : type1400 _119721) : (term139 _119721 op) = (term140 _119721 op).
Proof. exact (MK_COMB (@lem5713413 _119721 op) (@lem5713411 _119721 op)). Qed.
Lemma lem5713415 {_119721 : Type'} (op : type1400 _119721) : (term141 _119721 op) = (term139 _119721 op).
Proof. exact (@lem17045 (term32 _119721 op) (term25 _119721 op)). Qed.
Lemma lem5713416 {_119721 : Type'} (op : type1400 _119721) : (term141 _119721 op) = (term140 _119721 op).
Proof. exact (TRANS (@lem5713415 _119721 op) (@lem5713414 _119721 op)). Qed.
Lemma lem5713417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713418 {_119721 : Type'} (op : type1400 _119721) : (term142 _119721 op) = (term143 _119721 op).
Proof. exact (MK_COMB (@lem5713417) (@lem5713349 _119721 op)). Qed.
Lemma lem5713419 {_119721 : Type'} (op : type1400 _119721) : (term144 _119721 op) = (term145 _119721 op).
Proof. exact (MK_COMB (@lem5713418 _119721 op) (@lem5713416 _119721 op)). Qed.
Lemma lem5713420 {_119721 : Type'} (op : type1400 _119721) : (term146 _119721 op) = (term144 _119721 op).
Proof. exact (@lem17045 (term38 _119721 op) (term34 _119721 op)). Qed.
Lemma lem5713421 {_119721 : Type'} (op : type1400 _119721) : (term146 _119721 op) = (term145 _119721 op).
Proof. exact (TRANS (@lem5713420 _119721 op) (@lem5713419 _119721 op)). Qed.
Lemma lem5713422 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713423 {_119721 : Type'} (op : type1400 _119721) : (term147 _119721 op) = (term148 _119721 op).
Proof. exact (MK_COMB (@lem5713422) (@lem5713328 _119721 op)). Qed.
Lemma lem5713424 {_119721 : Type'} (op : type1400 _119721) : (term149 _119721 op) = (term150 _119721 op).
Proof. exact (MK_COMB (@lem5713423 _119721 op) (@lem5713421 _119721 op)). Qed.
Lemma lem5713425 {_119721 : Type'} (op : type1400 _119721) : (term151 _119721 op) = (term149 _119721 op).
Proof. exact (@lem17045 (term43 _119721 op) (term40 _119721 op)). Qed.
Lemma lem5713426 {_119721 : Type'} (op : type1400 _119721) : (term151 _119721 op) = (term150 _119721 op).
Proof. exact (TRANS (@lem5713425 _119721 op) (@lem5713424 _119721 op)). Qed.
Lemma lem5713427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713428 {_119721 : Type'} (op : type1400 _119721) : (term152 _119721 op) = (term153 _119721 op).
Proof. exact (MK_COMB (@lem5713427) (@lem5713317 _119721 op)). Qed.
Lemma lem5713429 {_119721 : Type'} (op : type1400 _119721) : (term154 _119721 op) = (term155 _119721 op).
Proof. exact (MK_COMB (@lem5713428 _119721 op) (@lem5713426 _119721 op)). Qed.
Lemma lem5713430 {_119721 : Type'} (op : type1400 _119721) : (term59 _119721 op) = (term154 _119721 op).
Proof. exact (@lem17045 (term48 _119721 op) (term45 _119721 op)). Qed.
Lemma lem5713431 {_119721 : Type'} (op : type1400 _119721) : (term59 _119721 op) = (term155 _119721 op).
Proof. exact (TRANS (@lem5713430 _119721 op) (@lem5713429 _119721 op)). Qed.
Lemma lem5713474 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5713475 {_119721 : Type'} (P : _119721 -> Prop) (Q : _119721 -> Prop) : (term156 _119721 P Q) = (term157 _119721 P Q).
Proof. exact (@lem5713474 _119721 P Q). Qed.
Lemma lem5713476 {_119721 : Type'} (op : type1400 _119721) : (term158 _119721 op) = (term159 _119721 op).
Proof. exact (@lem5713475 _119721 (term113 _119721 op) (term135 _119721 op)). Qed.
Lemma lem5713477 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term160 _119721 op a) = (term107 _119721 a op).
Proof. exact (eq_refl (term160 _119721 op a)). Qed.
Lemma lem5713478 {_119721 : Type'} (op : type1400 _119721) : (term161 _119721 op) = (term113 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713477 _119721 a op)). Qed.
Lemma lem5713479 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713480 {_119721 : Type'} (op : type1400 _119721) : (term162 _119721 op) = (term114 _119721 op).
Proof. exact (MK_COMB (@lem5713479 _119721) (@lem5713478 _119721 op)). Qed.
Lemma lem5713481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713482 {_119721 : Type'} (op : type1400 _119721) : (term163 _119721 op) = (term138 _119721 op).
Proof. exact (MK_COMB (@lem5713481) (@lem5713480 _119721 op)). Qed.
Lemma lem5713483 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term164 _119721 op a) = (term129 _119721 op a).
Proof. exact (eq_refl (term164 _119721 op a)). Qed.
Lemma lem5713484 {_119721 : Type'} (op : type1400 _119721) : (term165 _119721 op) = (term135 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713483 _119721 op a)). Qed.
Lemma lem5713485 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713486 {_119721 : Type'} (op : type1400 _119721) : (term166 _119721 op) = (term136 _119721 op).
Proof. exact (MK_COMB (@lem5713485 _119721) (@lem5713484 _119721 op)). Qed.
Lemma lem5713487 {_119721 : Type'} (op : type1400 _119721) : (term158 _119721 op) = (term140 _119721 op).
Proof. exact (MK_COMB (@lem5713482 _119721 op) (@lem5713486 _119721 op)). Qed.
Lemma lem5713488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713489 {_119721 : Type'} (op : type1400 _119721) : (term167 _119721 op) = (term168 _119721 op).
Proof. exact (MK_COMB (@lem5713488) (@lem5713487 _119721 op)). Qed.
Lemma lem5713490 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term160 _119721 op a) = (term107 _119721 a op).
Proof. exact (eq_refl (term160 _119721 op a)). Qed.
Lemma lem5713491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713492 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term169 _119721 op a) = (term170 _119721 a op).
Proof. exact (MK_COMB (@lem5713491) (@lem5713490 _119721 a op)). Qed.
Lemma lem5713493 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term164 _119721 op a) = (term129 _119721 op a).
Proof. exact (eq_refl (term164 _119721 op a)). Qed.
Lemma lem5713494 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term171 _119721 op a) = (term172 _119721 op a).
Proof. exact (MK_COMB (@lem5713492 _119721 a op) (@lem5713493 _119721 op a)). Qed.
Lemma lem5713495 {_119721 : Type'} (op : type1400 _119721) : (term173 _119721 op) = (term174 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713494 _119721 op a)). Qed.
Lemma lem5713496 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713497 {_119721 : Type'} (op : type1400 _119721) : (term159 _119721 op) = (term175 _119721 op).
Proof. exact (MK_COMB (@lem5713496 _119721) (@lem5713495 _119721 op)). Qed.
Lemma lem5713498 {_119721 : Type'} (op : type1400 _119721) : ((term158 _119721 op) = (term159 _119721 op)) = ((term140 _119721 op) = (term175 _119721 op)).
Proof. exact (MK_COMB (@lem5713489 _119721 op) (@lem5713497 _119721 op)). Qed.
Lemma lem5713499 {_119721 : Type'} (op : type1400 _119721) : (term140 _119721 op) = (term175 _119721 op).
Proof. exact (EQ_MP (@lem5713498 _119721 op) (@lem5713476 _119721 op)). Qed.
Lemma lem5713501 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5713502 {_119721 : Type'} (P : _119721 -> Prop) (Q : _119721 -> Prop) : (term156 _119721 P Q) = (term157 _119721 P Q).
Proof. exact (@lem5713501 _119721 P Q). Qed.
Lemma lem5713503 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term176 _119721 op a) = (term177 _119721 op a).
Proof. exact (@lem5713502 _119721 (term106 _119721 a op) (term128 _119721 op a)). Qed.
Lemma lem5713504 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term178 _119721 a op b) = (term100 _119721 a op b).
Proof. exact (eq_refl (term178 _119721 a op b)). Qed.
Lemma lem5713505 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term179 _119721 a op) = (term106 _119721 a op).
Proof. exact (fun_ext (fun b : _119721 => @lem5713504 _119721 a op b)). Qed.
Lemma lem5713506 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713507 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term180 _119721 a op) = (term107 _119721 a op).
Proof. exact (MK_COMB (@lem5713506 _119721) (@lem5713505 _119721 a op)). Qed.
Lemma lem5713508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713509 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term181 _119721 a op) = (term170 _119721 a op).
Proof. exact (MK_COMB (@lem5713508) (@lem5713507 _119721 a op)). Qed.
Lemma lem5713510 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term182 _119721 op a b) = (term122 _119721 b op a).
Proof. exact (eq_refl (term182 _119721 op a b)). Qed.
Lemma lem5713511 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term183 _119721 op a) = (term128 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713510 _119721 b op a)). Qed.
Lemma lem5713512 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713513 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term184 _119721 op a) = (term129 _119721 op a).
Proof. exact (MK_COMB (@lem5713512 _119721) (@lem5713511 _119721 op a)). Qed.
Lemma lem5713514 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term176 _119721 op a) = (term172 _119721 op a).
Proof. exact (MK_COMB (@lem5713509 _119721 a op) (@lem5713513 _119721 op a)). Qed.
Lemma lem5713515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713516 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term185 _119721 op a) = (term186 _119721 op a).
Proof. exact (MK_COMB (@lem5713515) (@lem5713514 _119721 op a)). Qed.
Lemma lem5713517 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term178 _119721 a op b) = (term100 _119721 a op b).
Proof. exact (eq_refl (term178 _119721 a op b)). Qed.
Lemma lem5713518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713519 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term187 _119721 a op b) = (term188 _119721 a op b).
Proof. exact (MK_COMB (@lem5713518) (@lem5713517 _119721 a op b)). Qed.
Lemma lem5713520 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term182 _119721 op a b) = (term122 _119721 b op a).
Proof. exact (eq_refl (term182 _119721 op a b)). Qed.
Lemma lem5713521 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term189 _119721 op a b) = (term190 _119721 b op a).
Proof. exact (MK_COMB (@lem5713519 _119721 a op b) (@lem5713520 _119721 b op a)). Qed.
Lemma lem5713522 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term191 _119721 op a) = (term192 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713521 _119721 b op a)). Qed.
Lemma lem5713523 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713524 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term177 _119721 op a) = (term193 _119721 op a).
Proof. exact (MK_COMB (@lem5713523 _119721) (@lem5713522 _119721 op a)). Qed.
Lemma lem5713525 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term176 _119721 op a) = (term177 _119721 op a)) = ((term172 _119721 op a) = (term193 _119721 op a)).
Proof. exact (MK_COMB (@lem5713516 _119721 op a) (@lem5713524 _119721 op a)). Qed.
Lemma lem5713526 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term172 _119721 op a) = (term193 _119721 op a).
Proof. exact (EQ_MP (@lem5713525 _119721 op a) (@lem5713503 _119721 op a)). Qed.
Lemma lem5713528 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5713529 {_119721 : Type'} (P : _119721 -> Prop) (Q : _119721 -> Prop) : (term156 _119721 P Q) = (term157 _119721 P Q).
Proof. exact (@lem5713528 _119721 P Q). Qed.
Lemma lem5713530 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term194 _119721 b op a) = (term195 _119721 b op a).
Proof. exact (@lem5713529 _119721 (term99 _119721 a op b) (term121 _119721 b op a)). Qed.
Lemma lem5713531 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term196 _119721 a op b c) = (term97 _119721 a op b c).
Proof. exact (eq_refl (term196 _119721 a op b c)). Qed.
Lemma lem5713532 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term197 _119721 a op b) = (term99 _119721 a op b).
Proof. exact (fun_ext (fun c : _119721 => @lem5713531 _119721 a op b c)). Qed.
Lemma lem5713533 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713534 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term198 _119721 a op b) = (term100 _119721 a op b).
Proof. exact (MK_COMB (@lem5713533 _119721) (@lem5713532 _119721 a op b)). Qed.
Lemma lem5713535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713536 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) : (term199 _119721 a op b) = (term188 _119721 a op b).
Proof. exact (MK_COMB (@lem5713535) (@lem5713534 _119721 a op b)). Qed.
Lemma lem5713537 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term200 _119721 b op a c) = (term119 _119721 b op a c).
Proof. exact (eq_refl (term200 _119721 b op a c)). Qed.
Lemma lem5713538 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term201 _119721 b op a) = (term121 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713537 _119721 b op a c)). Qed.
Lemma lem5713539 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713540 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term202 _119721 b op a) = (term122 _119721 b op a).
Proof. exact (MK_COMB (@lem5713539 _119721) (@lem5713538 _119721 b op a)). Qed.
Lemma lem5713541 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term194 _119721 b op a) = (term190 _119721 b op a).
Proof. exact (MK_COMB (@lem5713536 _119721 a op b) (@lem5713540 _119721 b op a)). Qed.
Lemma lem5713542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713543 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term203 _119721 b op a) = (term204 _119721 b op a).
Proof. exact (MK_COMB (@lem5713542) (@lem5713541 _119721 b op a)). Qed.
Lemma lem5713544 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term196 _119721 a op b c) = (term97 _119721 a op b c).
Proof. exact (eq_refl (term196 _119721 a op b c)). Qed.
Lemma lem5713545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713546 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term205 _119721 a op b c) = (term206 _119721 a op b c).
Proof. exact (MK_COMB (@lem5713545) (@lem5713544 _119721 a op b c)). Qed.
Lemma lem5713547 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term200 _119721 b op a c) = (term119 _119721 b op a c).
Proof. exact (eq_refl (term200 _119721 b op a c)). Qed.
Lemma lem5713548 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term207 _119721 b op a c) = (term208 _119721 b op a c).
Proof. exact (MK_COMB (@lem5713546 _119721 a op b c) (@lem5713547 _119721 b op a c)). Qed.
Lemma lem5713549 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term209 _119721 b op a) = (term210 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713548 _119721 b op a c)). Qed.
Lemma lem5713550 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713551 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term195 _119721 b op a) = (term211 _119721 b op a).
Proof. exact (MK_COMB (@lem5713550 _119721) (@lem5713549 _119721 b op a)). Qed.
Lemma lem5713552 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : ((term194 _119721 b op a) = (term195 _119721 b op a)) = ((term190 _119721 b op a) = (term211 _119721 b op a)).
Proof. exact (MK_COMB (@lem5713543 _119721 b op a) (@lem5713551 _119721 b op a)). Qed.
Lemma lem5713553 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term190 _119721 b op a) = (term211 _119721 b op a).
Proof. exact (EQ_MP (@lem5713552 _119721 b op a) (@lem5713530 _119721 b op a)). Qed.
Lemma lem5713554 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term192 _119721 op a) = (term212 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713553 _119721 b op a)). Qed.
Lemma lem5713555 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713556 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term193 _119721 op a) = (term213 _119721 op a).
Proof. exact (MK_COMB (@lem5713555 _119721) (@lem5713554 _119721 op a)). Qed.
Lemma lem5713557 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term172 _119721 op a) = (term213 _119721 op a).
Proof. exact (TRANS (@lem5713526 _119721 op a) (@lem5713556 _119721 op a)). Qed.
Lemma lem5713558 {_119721 : Type'} (op : type1400 _119721) : (term174 _119721 op) = (term214 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713557 _119721 op a)). Qed.
Lemma lem5713559 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713560 {_119721 : Type'} (op : type1400 _119721) : (term175 _119721 op) = (term215 _119721 op).
Proof. exact (MK_COMB (@lem5713559 _119721) (@lem5713558 _119721 op)). Qed.
Lemma lem5713561 {_119721 : Type'} (op : type1400 _119721) : (term140 _119721 op) = (term215 _119721 op).
Proof. exact (TRANS (@lem5713499 _119721 op) (@lem5713560 _119721 op)). Qed.
Lemma lem5713562 {_119721 : Type'} (op : type1400 _119721) : (term143 _119721 op) = (term143 _119721 op).
Proof. exact (eq_refl (term143 _119721 op)). Qed.
Lemma lem5713563 {_119721 : Type'} (op : type1400 _119721) : (term145 _119721 op) = (term216 _119721 op).
Proof. exact (MK_COMB (@lem5713562 _119721 op) (@lem5713561 _119721 op)). Qed.
Lemma lem5713565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5713566 {_119721 : Type'} (P : _119721 -> Prop) (Q : _119721 -> Prop) : (term156 _119721 P Q) = (term157 _119721 P Q).
Proof. exact (@lem5713565 _119721 P Q). Qed.
Lemma lem5713567 {_119721 : Type'} (op : type1400 _119721) : (term217 _119721 op) = (term218 _119721 op).
Proof. exact (@lem5713566 _119721 (term91 _119721 op) (term214 _119721 op)). Qed.
Lemma lem5713568 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term219 _119721 op a) = (term85 _119721 op a).
Proof. exact (eq_refl (term219 _119721 op a)). Qed.
Lemma lem5713569 {_119721 : Type'} (op : type1400 _119721) : (term220 _119721 op) = (term91 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713568 _119721 op a)). Qed.
Lemma lem5713570 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713571 {_119721 : Type'} (op : type1400 _119721) : (term221 _119721 op) = (term92 _119721 op).
Proof. exact (MK_COMB (@lem5713570 _119721) (@lem5713569 _119721 op)). Qed.
Lemma lem5713572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713573 {_119721 : Type'} (op : type1400 _119721) : (term222 _119721 op) = (term143 _119721 op).
Proof. exact (MK_COMB (@lem5713572) (@lem5713571 _119721 op)). Qed.
Lemma lem5713574 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term223 _119721 op a) = (term213 _119721 op a).
Proof. exact (eq_refl (term223 _119721 op a)). Qed.
Lemma lem5713575 {_119721 : Type'} (op : type1400 _119721) : (term224 _119721 op) = (term214 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713574 _119721 op a)). Qed.
Lemma lem5713576 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713577 {_119721 : Type'} (op : type1400 _119721) : (term225 _119721 op) = (term215 _119721 op).
Proof. exact (MK_COMB (@lem5713576 _119721) (@lem5713575 _119721 op)). Qed.
Lemma lem5713578 {_119721 : Type'} (op : type1400 _119721) : (term217 _119721 op) = (term216 _119721 op).
Proof. exact (MK_COMB (@lem5713573 _119721 op) (@lem5713577 _119721 op)). Qed.
Lemma lem5713579 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713580 {_119721 : Type'} (op : type1400 _119721) : (term226 _119721 op) = (term227 _119721 op).
Proof. exact (MK_COMB (@lem5713579) (@lem5713578 _119721 op)). Qed.
Lemma lem5713581 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term219 _119721 op a) = (term85 _119721 op a).
Proof. exact (eq_refl (term219 _119721 op a)). Qed.
Lemma lem5713582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713583 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term228 _119721 op a) = (term229 _119721 op a).
Proof. exact (MK_COMB (@lem5713582) (@lem5713581 _119721 op a)). Qed.
Lemma lem5713584 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term223 _119721 op a) = (term213 _119721 op a).
Proof. exact (eq_refl (term223 _119721 op a)). Qed.
Lemma lem5713585 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term230 _119721 op a) = (term231 _119721 op a).
Proof. exact (MK_COMB (@lem5713583 _119721 op a) (@lem5713584 _119721 op a)). Qed.
Lemma lem5713586 {_119721 : Type'} (op : type1400 _119721) : (term232 _119721 op) = (term233 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713585 _119721 op a)). Qed.
Lemma lem5713587 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713588 {_119721 : Type'} (op : type1400 _119721) : (term218 _119721 op) = (term234 _119721 op).
Proof. exact (MK_COMB (@lem5713587 _119721) (@lem5713586 _119721 op)). Qed.
Lemma lem5713589 {_119721 : Type'} (op : type1400 _119721) : ((term217 _119721 op) = (term218 _119721 op)) = ((term216 _119721 op) = (term234 _119721 op)).
Proof. exact (MK_COMB (@lem5713580 _119721 op) (@lem5713588 _119721 op)). Qed.
Lemma lem5713590 {_119721 : Type'} (op : type1400 _119721) : (term216 _119721 op) = (term234 _119721 op).
Proof. exact (EQ_MP (@lem5713589 _119721 op) (@lem5713567 _119721 op)). Qed.
Lemma lem5713592 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5713593 {_119721 : Type'} (P : _119721 -> Prop) (Q : _119721 -> Prop) : (term156 _119721 P Q) = (term157 _119721 P Q).
Proof. exact (@lem5713592 _119721 P Q). Qed.
Lemma lem5713594 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term235 _119721 op a) = (term236 _119721 op a).
Proof. exact (@lem5713593 _119721 (term84 _119721 op a) (term212 _119721 op a)). Qed.
Lemma lem5713595 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term237 _119721 op a b) = (term82 _119721 op b a).
Proof. exact (eq_refl (term237 _119721 op a b)). Qed.
Lemma lem5713596 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term238 _119721 op a) = (term84 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713595 _119721 op b a)). Qed.
Lemma lem5713597 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713598 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term239 _119721 op a) = (term85 _119721 op a).
Proof. exact (MK_COMB (@lem5713597 _119721) (@lem5713596 _119721 op a)). Qed.
Lemma lem5713599 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713600 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term240 _119721 op a) = (term229 _119721 op a).
Proof. exact (MK_COMB (@lem5713599) (@lem5713598 _119721 op a)). Qed.
Lemma lem5713601 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term241 _119721 op a b) = (term211 _119721 b op a).
Proof. exact (eq_refl (term241 _119721 op a b)). Qed.
Lemma lem5713602 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term242 _119721 op a) = (term212 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713601 _119721 b op a)). Qed.
Lemma lem5713603 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713604 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term243 _119721 op a) = (term213 _119721 op a).
Proof. exact (MK_COMB (@lem5713603 _119721) (@lem5713602 _119721 op a)). Qed.
Lemma lem5713605 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term235 _119721 op a) = (term231 _119721 op a).
Proof. exact (MK_COMB (@lem5713600 _119721 op a) (@lem5713604 _119721 op a)). Qed.
Lemma lem5713606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713607 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term244 _119721 op a) = (term245 _119721 op a).
Proof. exact (MK_COMB (@lem5713606) (@lem5713605 _119721 op a)). Qed.
Lemma lem5713608 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term237 _119721 op a b) = (term82 _119721 op b a).
Proof. exact (eq_refl (term237 _119721 op a b)). Qed.
Lemma lem5713609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713610 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term246 _119721 op a b) = (term247 _119721 op b a).
Proof. exact (MK_COMB (@lem5713609) (@lem5713608 _119721 op b a)). Qed.
Lemma lem5713611 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term241 _119721 op a b) = (term211 _119721 b op a).
Proof. exact (eq_refl (term241 _119721 op a b)). Qed.
Lemma lem5713612 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term248 _119721 op a b) = (term249 _119721 b op a).
Proof. exact (MK_COMB (@lem5713610 _119721 op b a) (@lem5713611 _119721 b op a)). Qed.
Lemma lem5713613 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term250 _119721 op a) = (term251 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713612 _119721 b op a)). Qed.
Lemma lem5713614 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713615 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term236 _119721 op a) = (term252 _119721 op a).
Proof. exact (MK_COMB (@lem5713614 _119721) (@lem5713613 _119721 op a)). Qed.
Lemma lem5713616 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term235 _119721 op a) = (term236 _119721 op a)) = ((term231 _119721 op a) = (term252 _119721 op a)).
Proof. exact (MK_COMB (@lem5713607 _119721 op a) (@lem5713615 _119721 op a)). Qed.
Lemma lem5713617 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term231 _119721 op a) = (term252 _119721 op a).
Proof. exact (EQ_MP (@lem5713616 _119721 op a) (@lem5713594 _119721 op a)). Qed.
Lemma lem5713619 {A : Type'} (P : Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5713620 {_119721 : Type'} (P : Prop) (Q : _119721 -> Prop) : (term253 _119721 P Q) = (term254 _119721 P Q).
Proof. exact (@lem5713619 _119721 P Q). Qed.
Lemma lem5713621 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term255 _119721 b op a) = (term256 _119721 b op a).
Proof. exact (@lem5713620 _119721 (term82 _119721 op b a) (term210 _119721 b op a)). Qed.
Lemma lem5713622 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term257 _119721 b op a c) = (term208 _119721 b op a c).
Proof. exact (eq_refl (term257 _119721 b op a c)). Qed.
Lemma lem5713623 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term258 _119721 b op a) = (term210 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713622 _119721 b op a c)). Qed.
Lemma lem5713624 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713625 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term259 _119721 b op a) = (term211 _119721 b op a).
Proof. exact (MK_COMB (@lem5713624 _119721) (@lem5713623 _119721 b op a)). Qed.
Lemma lem5713626 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term247 _119721 op b a) = (term247 _119721 op b a).
Proof. exact (eq_refl (term247 _119721 op b a)). Qed.
Lemma lem5713627 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term255 _119721 b op a) = (term249 _119721 b op a).
Proof. exact (MK_COMB (@lem5713626 _119721 op b a) (@lem5713625 _119721 b op a)). Qed.
Lemma lem5713628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713629 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term260 _119721 b op a) = (term261 _119721 b op a).
Proof. exact (MK_COMB (@lem5713628) (@lem5713627 _119721 b op a)). Qed.
Lemma lem5713630 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term257 _119721 b op a c) = (term208 _119721 b op a c).
Proof. exact (eq_refl (term257 _119721 b op a c)). Qed.
Lemma lem5713631 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term247 _119721 op b a) = (term247 _119721 op b a).
Proof. exact (eq_refl (term247 _119721 op b a)). Qed.
Lemma lem5713632 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term262 _119721 b op a c) = (term263 _119721 b op a c).
Proof. exact (MK_COMB (@lem5713631 _119721 op b a) (@lem5713630 _119721 b op a c)). Qed.
Lemma lem5713633 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term264 _119721 b op a) = (term265 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713632 _119721 b op a c)). Qed.
Lemma lem5713634 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713635 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term256 _119721 b op a) = (term266 _119721 b op a).
Proof. exact (MK_COMB (@lem5713634 _119721) (@lem5713633 _119721 b op a)). Qed.
Lemma lem5713636 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : ((term255 _119721 b op a) = (term256 _119721 b op a)) = ((term249 _119721 b op a) = (term266 _119721 b op a)).
Proof. exact (MK_COMB (@lem5713629 _119721 b op a) (@lem5713635 _119721 b op a)). Qed.
Lemma lem5713637 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term249 _119721 b op a) = (term266 _119721 b op a).
Proof. exact (EQ_MP (@lem5713636 _119721 b op a) (@lem5713621 _119721 b op a)). Qed.
Lemma lem5713638 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term251 _119721 op a) = (term267 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713637 _119721 b op a)). Qed.
Lemma lem5713639 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713640 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term252 _119721 op a) = (term268 _119721 op a).
Proof. exact (MK_COMB (@lem5713639 _119721) (@lem5713638 _119721 op a)). Qed.
Lemma lem5713641 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term231 _119721 op a) = (term268 _119721 op a).
Proof. exact (TRANS (@lem5713617 _119721 op a) (@lem5713640 _119721 op a)). Qed.
Lemma lem5713642 {_119721 : Type'} (op : type1400 _119721) : (term233 _119721 op) = (term269 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713641 _119721 op a)). Qed.
Lemma lem5713643 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713644 {_119721 : Type'} (op : type1400 _119721) : (term234 _119721 op) = (term270 _119721 op).
Proof. exact (MK_COMB (@lem5713643 _119721) (@lem5713642 _119721 op)). Qed.
Lemma lem5713645 {_119721 : Type'} (op : type1400 _119721) : (term216 _119721 op) = (term270 _119721 op).
Proof. exact (TRANS (@lem5713590 _119721 op) (@lem5713644 _119721 op)). Qed.
Lemma lem5713646 {_119721 : Type'} (op : type1400 _119721) : (term145 _119721 op) = (term270 _119721 op).
Proof. exact (TRANS (@lem5713563 _119721 op) (@lem5713645 _119721 op)). Qed.
Lemma lem5713647 {_119721 : Type'} (op : type1400 _119721) : (term148 _119721 op) = (term148 _119721 op).
Proof. exact (eq_refl (term148 _119721 op)). Qed.
Lemma lem5713648 {_119721 : Type'} (op : type1400 _119721) : (term150 _119721 op) = (term271 _119721 op).
Proof. exact (MK_COMB (@lem5713647 _119721 op) (@lem5713646 _119721 op)). Qed.
Lemma lem5713650 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5713651 {_119721 : Type'} (P : _119721 -> Prop) (Q : _119721 -> Prop) : (term156 _119721 P Q) = (term157 _119721 P Q).
Proof. exact (@lem5713650 _119721 P Q). Qed.
Lemma lem5713652 {_119721 : Type'} (op : type1400 _119721) : (term272 _119721 op) = (term273 _119721 op).
Proof. exact (@lem5713651 _119721 (term76 _119721 op) (term269 _119721 op)). Qed.
Lemma lem5713653 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term274 _119721 op a) = (term74 _119721 op a).
Proof. exact (eq_refl (term274 _119721 op a)). Qed.
Lemma lem5713654 {_119721 : Type'} (op : type1400 _119721) : (term275 _119721 op) = (term76 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713653 _119721 op a)). Qed.
Lemma lem5713655 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713656 {_119721 : Type'} (op : type1400 _119721) : (term276 _119721 op) = (term77 _119721 op).
Proof. exact (MK_COMB (@lem5713655 _119721) (@lem5713654 _119721 op)). Qed.
Lemma lem5713657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713658 {_119721 : Type'} (op : type1400 _119721) : (term277 _119721 op) = (term148 _119721 op).
Proof. exact (MK_COMB (@lem5713657) (@lem5713656 _119721 op)). Qed.
Lemma lem5713659 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term278 _119721 op a) = (term268 _119721 op a).
Proof. exact (eq_refl (term278 _119721 op a)). Qed.
Lemma lem5713660 {_119721 : Type'} (op : type1400 _119721) : (term279 _119721 op) = (term269 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713659 _119721 op a)). Qed.
Lemma lem5713661 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713662 {_119721 : Type'} (op : type1400 _119721) : (term280 _119721 op) = (term270 _119721 op).
Proof. exact (MK_COMB (@lem5713661 _119721) (@lem5713660 _119721 op)). Qed.
Lemma lem5713663 {_119721 : Type'} (op : type1400 _119721) : (term272 _119721 op) = (term271 _119721 op).
Proof. exact (MK_COMB (@lem5713658 _119721 op) (@lem5713662 _119721 op)). Qed.
Lemma lem5713664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713665 {_119721 : Type'} (op : type1400 _119721) : (term281 _119721 op) = (term282 _119721 op).
Proof. exact (MK_COMB (@lem5713664) (@lem5713663 _119721 op)). Qed.
Lemma lem5713666 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term274 _119721 op a) = (term74 _119721 op a).
Proof. exact (eq_refl (term274 _119721 op a)). Qed.
Lemma lem5713667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713668 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term283 _119721 op a) = (term284 _119721 op a).
Proof. exact (MK_COMB (@lem5713667) (@lem5713666 _119721 op a)). Qed.
Lemma lem5713669 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term278 _119721 op a) = (term268 _119721 op a).
Proof. exact (eq_refl (term278 _119721 op a)). Qed.
Lemma lem5713670 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term285 _119721 op a) = (term286 _119721 op a).
Proof. exact (MK_COMB (@lem5713668 _119721 op a) (@lem5713669 _119721 op a)). Qed.
Lemma lem5713671 {_119721 : Type'} (op : type1400 _119721) : (term287 _119721 op) = (term288 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713670 _119721 op a)). Qed.
Lemma lem5713672 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713673 {_119721 : Type'} (op : type1400 _119721) : (term273 _119721 op) = (term289 _119721 op).
Proof. exact (MK_COMB (@lem5713672 _119721) (@lem5713671 _119721 op)). Qed.
Lemma lem5713674 {_119721 : Type'} (op : type1400 _119721) : ((term272 _119721 op) = (term273 _119721 op)) = ((term271 _119721 op) = (term289 _119721 op)).
Proof. exact (MK_COMB (@lem5713665 _119721 op) (@lem5713673 _119721 op)). Qed.
Lemma lem5713675 {_119721 : Type'} (op : type1400 _119721) : (term271 _119721 op) = (term289 _119721 op).
Proof. exact (EQ_MP (@lem5713674 _119721 op) (@lem5713652 _119721 op)). Qed.
Lemma lem5713677 {A : Type'} (P : Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5713678 {_119721 : Type'} (P : Prop) (Q : _119721 -> Prop) : (term253 _119721 P Q) = (term254 _119721 P Q).
Proof. exact (@lem5713677 _119721 P Q). Qed.
Lemma lem5713679 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term290 _119721 op a) = (term291 _119721 op a).
Proof. exact (@lem5713678 _119721 (term74 _119721 op a) (term267 _119721 op a)). Qed.
Lemma lem5713680 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term292 _119721 op a b) = (term266 _119721 b op a).
Proof. exact (eq_refl (term292 _119721 op a b)). Qed.
Lemma lem5713681 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term293 _119721 op a) = (term267 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713680 _119721 b op a)). Qed.
Lemma lem5713682 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713683 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term294 _119721 op a) = (term268 _119721 op a).
Proof. exact (MK_COMB (@lem5713682 _119721) (@lem5713681 _119721 op a)). Qed.
Lemma lem5713684 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term284 _119721 op a) = (term284 _119721 op a).
Proof. exact (eq_refl (term284 _119721 op a)). Qed.
Lemma lem5713685 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term290 _119721 op a) = (term286 _119721 op a).
Proof. exact (MK_COMB (@lem5713684 _119721 op a) (@lem5713683 _119721 op a)). Qed.
Lemma lem5713686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713687 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term295 _119721 op a) = (term296 _119721 op a).
Proof. exact (MK_COMB (@lem5713686) (@lem5713685 _119721 op a)). Qed.
Lemma lem5713688 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term292 _119721 op a b) = (term266 _119721 b op a).
Proof. exact (eq_refl (term292 _119721 op a b)). Qed.
Lemma lem5713689 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term284 _119721 op a) = (term284 _119721 op a).
Proof. exact (eq_refl (term284 _119721 op a)). Qed.
Lemma lem5713690 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term297 _119721 op a b) = (term298 _119721 b op a).
Proof. exact (MK_COMB (@lem5713689 _119721 op a) (@lem5713688 _119721 b op a)). Qed.
Lemma lem5713691 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term299 _119721 op a) = (term300 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713690 _119721 b op a)). Qed.
Lemma lem5713692 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713693 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term291 _119721 op a) = (term301 _119721 op a).
Proof. exact (MK_COMB (@lem5713692 _119721) (@lem5713691 _119721 op a)). Qed.
Lemma lem5713694 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term290 _119721 op a) = (term291 _119721 op a)) = ((term286 _119721 op a) = (term301 _119721 op a)).
Proof. exact (MK_COMB (@lem5713687 _119721 op a) (@lem5713693 _119721 op a)). Qed.
Lemma lem5713695 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term286 _119721 op a) = (term301 _119721 op a).
Proof. exact (EQ_MP (@lem5713694 _119721 op a) (@lem5713679 _119721 op a)). Qed.
Lemma lem5713697 {A : Type'} (P : Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5713698 {_119721 : Type'} (P : Prop) (Q : _119721 -> Prop) : (term253 _119721 P Q) = (term254 _119721 P Q).
Proof. exact (@lem5713697 _119721 P Q). Qed.
Lemma lem5713699 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term302 _119721 b op a) = (term303 _119721 b op a).
Proof. exact (@lem5713698 _119721 (term74 _119721 op a) (term265 _119721 b op a)). Qed.
Lemma lem5713700 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term304 _119721 b op a c) = (term263 _119721 b op a c).
Proof. exact (eq_refl (term304 _119721 b op a c)). Qed.
Lemma lem5713701 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term305 _119721 b op a) = (term265 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713700 _119721 b op a c)). Qed.
Lemma lem5713702 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713703 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term306 _119721 b op a) = (term266 _119721 b op a).
Proof. exact (MK_COMB (@lem5713702 _119721) (@lem5713701 _119721 b op a)). Qed.
Lemma lem5713704 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term284 _119721 op a) = (term284 _119721 op a).
Proof. exact (eq_refl (term284 _119721 op a)). Qed.
Lemma lem5713705 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term302 _119721 b op a) = (term298 _119721 b op a).
Proof. exact (MK_COMB (@lem5713704 _119721 op a) (@lem5713703 _119721 b op a)). Qed.
Lemma lem5713706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713707 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term307 _119721 b op a) = (term308 _119721 b op a).
Proof. exact (MK_COMB (@lem5713706) (@lem5713705 _119721 b op a)). Qed.
Lemma lem5713708 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term304 _119721 b op a c) = (term263 _119721 b op a c).
Proof. exact (eq_refl (term304 _119721 b op a c)). Qed.
Lemma lem5713709 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term284 _119721 op a) = (term284 _119721 op a).
Proof. exact (eq_refl (term284 _119721 op a)). Qed.
Lemma lem5713710 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term309 _119721 b op a c) = (term310 _119721 b op a c).
Proof. exact (MK_COMB (@lem5713709 _119721 op a) (@lem5713708 _119721 b op a c)). Qed.
Lemma lem5713711 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term311 _119721 b op a) = (term312 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713710 _119721 b op a c)). Qed.
Lemma lem5713712 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713713 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term303 _119721 b op a) = (term313 _119721 b op a).
Proof. exact (MK_COMB (@lem5713712 _119721) (@lem5713711 _119721 b op a)). Qed.
Lemma lem5713714 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : ((term302 _119721 b op a) = (term303 _119721 b op a)) = ((term298 _119721 b op a) = (term313 _119721 b op a)).
Proof. exact (MK_COMB (@lem5713707 _119721 b op a) (@lem5713713 _119721 b op a)). Qed.
Lemma lem5713715 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term298 _119721 b op a) = (term313 _119721 b op a).
Proof. exact (EQ_MP (@lem5713714 _119721 b op a) (@lem5713699 _119721 b op a)). Qed.
Lemma lem5713716 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term300 _119721 op a) = (term314 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713715 _119721 b op a)). Qed.
Lemma lem5713717 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713718 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term301 _119721 op a) = (term315 _119721 op a).
Proof. exact (MK_COMB (@lem5713717 _119721) (@lem5713716 _119721 op a)). Qed.
Lemma lem5713719 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term286 _119721 op a) = (term315 _119721 op a).
Proof. exact (TRANS (@lem5713695 _119721 op a) (@lem5713718 _119721 op a)). Qed.
Lemma lem5713720 {_119721 : Type'} (op : type1400 _119721) : (term288 _119721 op) = (term316 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713719 _119721 op a)). Qed.
Lemma lem5713721 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713722 {_119721 : Type'} (op : type1400 _119721) : (term289 _119721 op) = (term317 _119721 op).
Proof. exact (MK_COMB (@lem5713721 _119721) (@lem5713720 _119721 op)). Qed.
Lemma lem5713723 {_119721 : Type'} (op : type1400 _119721) : (term271 _119721 op) = (term317 _119721 op).
Proof. exact (TRANS (@lem5713675 _119721 op) (@lem5713722 _119721 op)). Qed.
Lemma lem5713724 {_119721 : Type'} (op : type1400 _119721) : (term150 _119721 op) = (term317 _119721 op).
Proof. exact (TRANS (@lem5713648 _119721 op) (@lem5713723 _119721 op)). Qed.
Lemma lem5713725 {_119721 : Type'} (op : type1400 _119721) : (term153 _119721 op) = (term153 _119721 op).
Proof. exact (eq_refl (term153 _119721 op)). Qed.
Lemma lem5713726 {_119721 : Type'} (op : type1400 _119721) : (term155 _119721 op) = (term318 _119721 op).
Proof. exact (MK_COMB (@lem5713725 _119721 op) (@lem5713724 _119721 op)). Qed.
Lemma lem5713728 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term156 A P Q) = (term157 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5713729 {_119721 : Type'} (P : _119721 -> Prop) (Q : _119721 -> Prop) : (term156 _119721 P Q) = (term157 _119721 P Q).
Proof. exact (@lem5713728 _119721 P Q). Qed.
Lemma lem5713730 {_119721 : Type'} (op : type1400 _119721) : (term319 _119721 op) = (term320 _119721 op).
Proof. exact (@lem5713729 _119721 (term68 _119721 op) (term316 _119721 op)). Qed.
Lemma lem5713731 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term321 _119721 op a) = (term66 _119721 op a).
Proof. exact (eq_refl (term321 _119721 op a)). Qed.
Lemma lem5713732 {_119721 : Type'} (op : type1400 _119721) : (term322 _119721 op) = (term68 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713731 _119721 op a)). Qed.
Lemma lem5713733 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713734 {_119721 : Type'} (op : type1400 _119721) : (term323 _119721 op) = (term69 _119721 op).
Proof. exact (MK_COMB (@lem5713733 _119721) (@lem5713732 _119721 op)). Qed.
Lemma lem5713735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713736 {_119721 : Type'} (op : type1400 _119721) : (term324 _119721 op) = (term153 _119721 op).
Proof. exact (MK_COMB (@lem5713735) (@lem5713734 _119721 op)). Qed.
Lemma lem5713737 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term325 _119721 op a) = (term315 _119721 op a).
Proof. exact (eq_refl (term325 _119721 op a)). Qed.
Lemma lem5713738 {_119721 : Type'} (op : type1400 _119721) : (term326 _119721 op) = (term316 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713737 _119721 op a)). Qed.
Lemma lem5713739 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713740 {_119721 : Type'} (op : type1400 _119721) : (term327 _119721 op) = (term317 _119721 op).
Proof. exact (MK_COMB (@lem5713739 _119721) (@lem5713738 _119721 op)). Qed.
Lemma lem5713741 {_119721 : Type'} (op : type1400 _119721) : (term319 _119721 op) = (term318 _119721 op).
Proof. exact (MK_COMB (@lem5713736 _119721 op) (@lem5713740 _119721 op)). Qed.
Lemma lem5713742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713743 {_119721 : Type'} (op : type1400 _119721) : (term328 _119721 op) = (term329 _119721 op).
Proof. exact (MK_COMB (@lem5713742) (@lem5713741 _119721 op)). Qed.
Lemma lem5713744 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term321 _119721 op a) = (term66 _119721 op a).
Proof. exact (eq_refl (term321 _119721 op a)). Qed.
Lemma lem5713745 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5713746 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term330 _119721 op a) = (term331 _119721 op a).
Proof. exact (MK_COMB (@lem5713745) (@lem5713744 _119721 op a)). Qed.
Lemma lem5713747 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term325 _119721 op a) = (term315 _119721 op a).
Proof. exact (eq_refl (term325 _119721 op a)). Qed.
Lemma lem5713748 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term332 _119721 op a) = (term333 _119721 op a).
Proof. exact (MK_COMB (@lem5713746 _119721 op a) (@lem5713747 _119721 op a)). Qed.
Lemma lem5713749 {_119721 : Type'} (op : type1400 _119721) : (term334 _119721 op) = (term335 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713748 _119721 op a)). Qed.
Lemma lem5713750 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713751 {_119721 : Type'} (op : type1400 _119721) : (term320 _119721 op) = (term336 _119721 op).
Proof. exact (MK_COMB (@lem5713750 _119721) (@lem5713749 _119721 op)). Qed.
Lemma lem5713752 {_119721 : Type'} (op : type1400 _119721) : ((term319 _119721 op) = (term320 _119721 op)) = ((term318 _119721 op) = (term336 _119721 op)).
Proof. exact (MK_COMB (@lem5713743 _119721 op) (@lem5713751 _119721 op)). Qed.
Lemma lem5713753 {_119721 : Type'} (op : type1400 _119721) : (term318 _119721 op) = (term336 _119721 op).
Proof. exact (EQ_MP (@lem5713752 _119721 op) (@lem5713730 _119721 op)). Qed.
Lemma lem5713755 {A : Type'} (P : Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5713756 {_119721 : Type'} (P : Prop) (Q : _119721 -> Prop) : (term253 _119721 P Q) = (term254 _119721 P Q).
Proof. exact (@lem5713755 _119721 P Q). Qed.
Lemma lem5713757 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term337 _119721 op a) = (term338 _119721 op a).
Proof. exact (@lem5713756 _119721 (term66 _119721 op a) (term314 _119721 op a)). Qed.
Lemma lem5713758 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term339 _119721 op a b) = (term313 _119721 b op a).
Proof. exact (eq_refl (term339 _119721 op a b)). Qed.
Lemma lem5713759 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term340 _119721 op a) = (term314 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713758 _119721 b op a)). Qed.
Lemma lem5713760 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713761 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term341 _119721 op a) = (term315 _119721 op a).
Proof. exact (MK_COMB (@lem5713760 _119721) (@lem5713759 _119721 op a)). Qed.
Lemma lem5713762 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term331 _119721 op a) = (term331 _119721 op a).
Proof. exact (eq_refl (term331 _119721 op a)). Qed.
Lemma lem5713763 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term337 _119721 op a) = (term333 _119721 op a).
Proof. exact (MK_COMB (@lem5713762 _119721 op a) (@lem5713761 _119721 op a)). Qed.
Lemma lem5713764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713765 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term342 _119721 op a) = (term343 _119721 op a).
Proof. exact (MK_COMB (@lem5713764) (@lem5713763 _119721 op a)). Qed.
Lemma lem5713766 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term339 _119721 op a b) = (term313 _119721 b op a).
Proof. exact (eq_refl (term339 _119721 op a b)). Qed.
Lemma lem5713767 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term331 _119721 op a) = (term331 _119721 op a).
Proof. exact (eq_refl (term331 _119721 op a)). Qed.
Lemma lem5713768 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term344 _119721 op a b) = (term345 _119721 b op a).
Proof. exact (MK_COMB (@lem5713767 _119721 op a) (@lem5713766 _119721 b op a)). Qed.
Lemma lem5713769 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term346 _119721 op a) = (term347 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713768 _119721 b op a)). Qed.
Lemma lem5713770 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713771 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term338 _119721 op a) = (term348 _119721 op a).
Proof. exact (MK_COMB (@lem5713770 _119721) (@lem5713769 _119721 op a)). Qed.
Lemma lem5713772 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term337 _119721 op a) = (term338 _119721 op a)) = ((term333 _119721 op a) = (term348 _119721 op a)).
Proof. exact (MK_COMB (@lem5713765 _119721 op a) (@lem5713771 _119721 op a)). Qed.
Lemma lem5713773 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term333 _119721 op a) = (term348 _119721 op a).
Proof. exact (EQ_MP (@lem5713772 _119721 op a) (@lem5713757 _119721 op a)). Qed.
Lemma lem5713775 {A : Type'} (P : Prop) (Q : A -> Prop) : (term253 A P Q) = (term254 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5713776 {_119721 : Type'} (P : Prop) (Q : _119721 -> Prop) : (term253 _119721 P Q) = (term254 _119721 P Q).
Proof. exact (@lem5713775 _119721 P Q). Qed.
Lemma lem5713777 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term349 _119721 b op a) = (term350 _119721 b op a).
Proof. exact (@lem5713776 _119721 (term66 _119721 op a) (term312 _119721 b op a)). Qed.
Lemma lem5713778 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term351 _119721 b op a c) = (term310 _119721 b op a c).
Proof. exact (eq_refl (term351 _119721 b op a c)). Qed.
Lemma lem5713779 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term352 _119721 b op a) = (term312 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713778 _119721 b op a c)). Qed.
Lemma lem5713780 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713781 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term353 _119721 b op a) = (term313 _119721 b op a).
Proof. exact (MK_COMB (@lem5713780 _119721) (@lem5713779 _119721 b op a)). Qed.
Lemma lem5713782 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term331 _119721 op a) = (term331 _119721 op a).
Proof. exact (eq_refl (term331 _119721 op a)). Qed.
Lemma lem5713783 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term349 _119721 b op a) = (term345 _119721 b op a).
Proof. exact (MK_COMB (@lem5713782 _119721 op a) (@lem5713781 _119721 b op a)). Qed.
Lemma lem5713784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5713785 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term354 _119721 b op a) = (term355 _119721 b op a).
Proof. exact (MK_COMB (@lem5713784) (@lem5713783 _119721 b op a)). Qed.
Lemma lem5713786 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term351 _119721 b op a c) = (term310 _119721 b op a c).
Proof. exact (eq_refl (term351 _119721 b op a c)). Qed.
Lemma lem5713787 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term331 _119721 op a) = (term331 _119721 op a).
Proof. exact (eq_refl (term331 _119721 op a)). Qed.
Lemma lem5713788 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term356 _119721 b op a c) = (term357 _119721 b op a c).
Proof. exact (MK_COMB (@lem5713787 _119721 op a) (@lem5713786 _119721 b op a c)). Qed.
Lemma lem5713789 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term358 _119721 b op a) = (term359 _119721 b op a).
Proof. exact (fun_ext (fun c : _119721 => @lem5713788 _119721 b op a c)). Qed.
Lemma lem5713790 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713791 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term350 _119721 b op a) = (term360 _119721 b op a).
Proof. exact (MK_COMB (@lem5713790 _119721) (@lem5713789 _119721 b op a)). Qed.
Lemma lem5713792 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : ((term349 _119721 b op a) = (term350 _119721 b op a)) = ((term345 _119721 b op a) = (term360 _119721 b op a)).
Proof. exact (MK_COMB (@lem5713785 _119721 b op a) (@lem5713791 _119721 b op a)). Qed.
Lemma lem5713793 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) : (term345 _119721 b op a) = (term360 _119721 b op a).
Proof. exact (EQ_MP (@lem5713792 _119721 b op a) (@lem5713777 _119721 b op a)). Qed.
Lemma lem5713794 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term347 _119721 op a) = (term361 _119721 op a).
Proof. exact (fun_ext (fun b : _119721 => @lem5713793 _119721 b op a)). Qed.
Lemma lem5713795 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713796 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term348 _119721 op a) = (term362 _119721 op a).
Proof. exact (MK_COMB (@lem5713795 _119721) (@lem5713794 _119721 op a)). Qed.
Lemma lem5713797 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term333 _119721 op a) = (term362 _119721 op a).
Proof. exact (TRANS (@lem5713773 _119721 op a) (@lem5713796 _119721 op a)). Qed.
Lemma lem5713798 {_119721 : Type'} (op : type1400 _119721) : (term335 _119721 op) = (term363 _119721 op).
Proof. exact (fun_ext (fun a : _119721 => @lem5713797 _119721 op a)). Qed.
Lemma lem5713799 {_119721 : Type'} : (@ex _119721) = (@ex _119721).
Proof. exact (eq_refl (@ex _119721)). Qed.
Lemma lem5713800 {_119721 : Type'} (op : type1400 _119721) : (term336 _119721 op) = (term364 _119721 op).
Proof. exact (MK_COMB (@lem5713799 _119721) (@lem5713798 _119721 op)). Qed.
Lemma lem5713801 {_119721 : Type'} (op : type1400 _119721) : (term318 _119721 op) = (term364 _119721 op).
Proof. exact (TRANS (@lem5713753 _119721 op) (@lem5713800 _119721 op)). Qed.
Lemma lem5713803 {_119721 : Type'} (op : type1400 _119721) : (term155 _119721 op) = (term364 _119721 op).
Proof. exact (TRANS (@lem5713726 _119721 op) (@lem5713801 _119721 op)). Qed.
Lemma lem5713804 {_119721 : Type'} (op : type1400 _119721) : (term59 _119721 op) = (term364 _119721 op).
Proof. exact (TRANS (@lem5713431 _119721 op) (@lem5713803 _119721 op)). Qed.
Lemma lem5713805 {_119721 : Type'} (op : type1400 _119721) (h1 : term59 _119721 op) : term364 _119721 op.
Proof. exact (EQ_MP (@lem5713804 _119721 op) (@lem5713250 _119721 op h1)). Qed.
Lemma lem5713806 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (h1 : term362 _119721 op a) : term362 _119721 op a.
Proof. exact (h1). Qed.
Lemma lem5713807 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (h1 : term360 _119721 b op a) : term360 _119721 b op a.
Proof. exact (h1). Qed.
Lemma lem5713808 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term357 _119721 b op a c) : term357 _119721 b op a c.
Proof. exact (h1). Qed.
Lemma lem5713809 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5713818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713819 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713818 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713820 {_119721 : Type'} (op : type1400 _119721) : (term365 _119721 op) = (term366 _119721 op).
Proof. exact (@lem5713819 _119721 op (@neutral _119721 op)). Qed.
Lemma lem5713821 {_119721 : Type'} (x : _119721) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5713822 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term46 _119721 op x) = (term367 _119721 op x).
Proof. exact (MK_COMB (@lem5713820 _119721 op) (@lem5713821 _119721 x)). Qed.
Lemma lem5713824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713825 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713824 _119721 _119721 f x). Qed.
Lemma lem5713826 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term367 _119721 op x) = (term368 _119721 op x).
Proof. exact (@lem5713825 _119721 (term366 _119721 op) x). Qed.
Lemma lem5713828 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term46 _119721 op x) = (term368 _119721 op x).
Proof. exact (TRANS (@lem5713822 _119721 op x) (@lem5713826 _119721 op x)). Qed.
Lemma lem5713829 {_119721 : Type'} (x : _119721) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5713830 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term369 _119721 op x) = (term370 _119721 op x).
Proof. exact (MK_COMB (@lem5713809 _119721) (@lem5713828 _119721 op x)). Qed.
Lemma lem5713831 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : ((term46 _119721 op x) = x) = ((term368 _119721 op x) = x).
Proof. exact (MK_COMB (@lem5713830 _119721 op x) (@lem5713829 _119721 x)). Qed.
Lemma lem5713832 {_119721 : Type'} (op : type1400 _119721) : (term47 _119721 op) = (term371 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713831 _119721 op x)). Qed.
Lemma lem5713833 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713834 {_119721 : Type'} (op : type1400 _119721) : (term48 _119721 op) = (term372 _119721 op).
Proof. exact (MK_COMB (@lem5713833 _119721) (@lem5713832 _119721 op)). Qed.
Lemma lem5713835 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5713844 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713845 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713844 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713846 {_119721 : Type'} (op : type1400 _119721) (y : _119721) : (op y) = (@I (_119721 -> _119721 -> _119721) op y).
Proof. exact (@lem5713845 _119721 op y). Qed.
Lemma lem5713847 {_119721 : Type'} (z : _119721) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5713848 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (z : _119721) : (op y z) = (@I (_119721 -> _119721 -> _119721) op y z).
Proof. exact (MK_COMB (@lem5713846 _119721 op y) (@lem5713847 _119721 z)). Qed.
Lemma lem5713850 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713851 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713850 _119721 _119721 f x). Qed.
Lemma lem5713852 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (z : _119721) : (@I (_119721 -> _119721 -> _119721) op y z) = (term373 _119721 op y z).
Proof. exact (@lem5713851 _119721 (@I (_119721 -> _119721 -> _119721) op y) z). Qed.
Lemma lem5713854 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (z : _119721) : (op y z) = (term373 _119721 op y z).
Proof. exact (TRANS (@lem5713848 _119721 op y z) (@lem5713852 _119721 op y z)). Qed.
Lemma lem5713855 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (op x) = (op x).
Proof. exact (eq_refl (op x)). Qed.
Lemma lem5713856 {_119721 : Type'} (x : _119721) (op : type1400 _119721) (y : _119721) (z : _119721) : (term19 _119721 x op y z) = (term374 _119721 x op y z).
Proof. exact (MK_COMB (@lem5713855 _119721 op x) (@lem5713854 _119721 op y z)). Qed.
Lemma lem5713858 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713859 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713858 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713860 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (op x) = (@I (_119721 -> _119721 -> _119721) op x).
Proof. exact (@lem5713859 _119721 op x). Qed.
Lemma lem5713861 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (z : _119721) : (term373 _119721 op y z) = (term373 _119721 op y z).
Proof. exact (eq_refl (term373 _119721 op y z)). Qed.
Lemma lem5713862 {_119721 : Type'} (x : _119721) (op : type1400 _119721) (y : _119721) (z : _119721) : (term374 _119721 x op y z) = (term375 _119721 x op y z).
Proof. exact (MK_COMB (@lem5713860 _119721 op x) (@lem5713861 _119721 op y z)). Qed.
Lemma lem5713864 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713865 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713864 _119721 _119721 f x). Qed.
Lemma lem5713866 {_119721 : Type'} (x : _119721) (op : type1400 _119721) (y : _119721) (z : _119721) : (term375 _119721 x op y z) = (term376 _119721 x op y z).
Proof. exact (@lem5713865 _119721 (@I (_119721 -> _119721 -> _119721) op x) (term373 _119721 op y z)). Qed.
Lemma lem5713867 {_119721 : Type'} (x : _119721) (op : type1400 _119721) (y : _119721) (z : _119721) : (term374 _119721 x op y z) = (term376 _119721 x op y z).
Proof. exact (TRANS (@lem5713862 _119721 x op y z) (@lem5713866 _119721 x op y z)). Qed.
Lemma lem5713868 {_119721 : Type'} (x : _119721) (op : type1400 _119721) (y : _119721) (z : _119721) : (term19 _119721 x op y z) = (term376 _119721 x op y z).
Proof. exact (TRANS (@lem5713856 _119721 x op y z) (@lem5713867 _119721 x op y z)). Qed.
Lemma lem5713869 {_119721 : Type'} (op : type1400 _119721) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5713876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713877 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713876 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713878 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (op x) = (@I (_119721 -> _119721 -> _119721) op x).
Proof. exact (@lem5713877 _119721 op x). Qed.
Lemma lem5713879 {_119721 : Type'} (y : _119721) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5713880 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (op x y) = (@I (_119721 -> _119721 -> _119721) op x y).
Proof. exact (MK_COMB (@lem5713878 _119721 op x) (@lem5713879 _119721 y)). Qed.
Lemma lem5713882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713883 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713882 _119721 _119721 f x). Qed.
Lemma lem5713884 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (@I (_119721 -> _119721 -> _119721) op x y) = (term373 _119721 op x y).
Proof. exact (@lem5713883 _119721 (@I (_119721 -> _119721 -> _119721) op x) y). Qed.
Lemma lem5713886 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (op x y) = (term373 _119721 op x y).
Proof. exact (TRANS (@lem5713880 _119721 op x y) (@lem5713884 _119721 op x y)). Qed.
Lemma lem5713887 {_119721 : Type'} (z : _119721) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5713888 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term377 _119721 op x y) = (term378 _119721 op x y).
Proof. exact (MK_COMB (@lem5713869 _119721 op) (@lem5713886 _119721 op x y)). Qed.
Lemma lem5713889 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : (term26 _119721 op x y z) = (term379 _119721 op x y z).
Proof. exact (MK_COMB (@lem5713888 _119721 op x y) (@lem5713887 _119721 z)). Qed.
Lemma lem5713891 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713892 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713891 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713893 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term378 _119721 op x y) = (term380 _119721 op x y).
Proof. exact (@lem5713892 _119721 op (term373 _119721 op x y)). Qed.
Lemma lem5713894 {_119721 : Type'} (z : _119721) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5713895 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : (term379 _119721 op x y z) = (term381 _119721 op x y z).
Proof. exact (MK_COMB (@lem5713893 _119721 op x y) (@lem5713894 _119721 z)). Qed.
Lemma lem5713897 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713898 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713897 _119721 _119721 f x). Qed.
Lemma lem5713899 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : (term381 _119721 op x y z) = (term382 _119721 op x y z).
Proof. exact (@lem5713898 _119721 (term380 _119721 op x y) z). Qed.
Lemma lem5713900 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : (term379 _119721 op x y z) = (term382 _119721 op x y z).
Proof. exact (TRANS (@lem5713895 _119721 op x y z) (@lem5713899 _119721 op x y z)). Qed.
Lemma lem5713901 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : (term26 _119721 op x y z) = (term382 _119721 op x y z).
Proof. exact (TRANS (@lem5713889 _119721 op x y z) (@lem5713900 _119721 op x y z)). Qed.
Lemma lem5713902 {_119721 : Type'} (x : _119721) (op : type1400 _119721) (y : _119721) (z : _119721) : (term383 _119721 x op y z) = (term384 _119721 x op y z).
Proof. exact (MK_COMB (@lem5713835 _119721) (@lem5713868 _119721 x op y z)). Qed.
Lemma lem5713903 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : ((term19 _119721 x op y z) = (term26 _119721 op x y z)) = ((term376 _119721 x op y z) = (term382 _119721 op x y z)).
Proof. exact (MK_COMB (@lem5713902 _119721 x op y z) (@lem5713901 _119721 op x y z)). Qed.
Lemma lem5713904 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term50 _119721 op x y) = (term385 _119721 op x y).
Proof. exact (fun_ext (fun z : _119721 => @lem5713903 _119721 op x y z)). Qed.
Lemma lem5713905 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713906 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term51 _119721 op x y) = (term386 _119721 op x y).
Proof. exact (MK_COMB (@lem5713905 _119721) (@lem5713904 _119721 op x y)). Qed.
Lemma lem5713907 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term52 _119721 op x) = (term387 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5713906 _119721 op x y)). Qed.
Lemma lem5713908 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713909 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term53 _119721 op x) = (term388 _119721 op x).
Proof. exact (MK_COMB (@lem5713908 _119721) (@lem5713907 _119721 op x)). Qed.
Lemma lem5713910 {_119721 : Type'} (op : type1400 _119721) : (term54 _119721 op) = (term389 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713909 _119721 op x)). Qed.
Lemma lem5713911 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713912 {_119721 : Type'} (op : type1400 _119721) : (term55 _119721 op) = (term390 _119721 op).
Proof. exact (MK_COMB (@lem5713911 _119721) (@lem5713910 _119721 op)). Qed.
Lemma lem5713913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713914 {_119721 : Type'} (op : type1400 _119721) : (term56 _119721 op) = (term391 _119721 op).
Proof. exact (MK_COMB (@lem5713913) (@lem5713912 _119721 op)). Qed.
Lemma lem5713915 {_119721 : Type'} (op : type1400 _119721) : (term57 _119721 op) = (term392 _119721 op).
Proof. exact (MK_COMB (@lem5713914 _119721 op) (@lem5713834 _119721 op)). Qed.
Lemma lem5713916 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5713923 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713924 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713923 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713925 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (op x) = (@I (_119721 -> _119721 -> _119721) op x).
Proof. exact (@lem5713924 _119721 op x). Qed.
Lemma lem5713926 {_119721 : Type'} (y : _119721) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5713927 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (op x y) = (@I (_119721 -> _119721 -> _119721) op x y).
Proof. exact (MK_COMB (@lem5713925 _119721 op x) (@lem5713926 _119721 y)). Qed.
Lemma lem5713929 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713930 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713929 _119721 _119721 f x). Qed.
Lemma lem5713931 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (@I (_119721 -> _119721 -> _119721) op x y) = (term373 _119721 op x y).
Proof. exact (@lem5713930 _119721 (@I (_119721 -> _119721 -> _119721) op x) y). Qed.
Lemma lem5713933 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (op x y) = (term373 _119721 op x y).
Proof. exact (TRANS (@lem5713927 _119721 op x y) (@lem5713931 _119721 op x y)). Qed.
Lemma lem5713940 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713941 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713940 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713942 {_119721 : Type'} (op : type1400 _119721) (y : _119721) : (op y) = (@I (_119721 -> _119721 -> _119721) op y).
Proof. exact (@lem5713941 _119721 op y). Qed.
Lemma lem5713943 {_119721 : Type'} (x : _119721) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5713944 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : (op y x) = (@I (_119721 -> _119721 -> _119721) op y x).
Proof. exact (MK_COMB (@lem5713942 _119721 op y) (@lem5713943 _119721 x)). Qed.
Lemma lem5713946 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713947 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713946 _119721 _119721 f x). Qed.
Lemma lem5713948 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : (@I (_119721 -> _119721 -> _119721) op y x) = (term373 _119721 op y x).
Proof. exact (@lem5713947 _119721 (@I (_119721 -> _119721 -> _119721) op y) x). Qed.
Lemma lem5713950 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : (op y x) = (term373 _119721 op y x).
Proof. exact (TRANS (@lem5713944 _119721 op y x) (@lem5713948 _119721 op y x)). Qed.
Lemma lem5713951 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term393 _119721 op x y) = (term394 _119721 op x y).
Proof. exact (MK_COMB (@lem5713916 _119721) (@lem5713933 _119721 op x y)). Qed.
Lemma lem5713952 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : ((op x y) = (op y x)) = ((term373 _119721 op x y) = (term373 _119721 op y x)).
Proof. exact (MK_COMB (@lem5713951 _119721 op x y) (@lem5713950 _119721 op y x)). Qed.
Lemma lem5713953 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term35 _119721 op x) = (term395 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5713952 _119721 op y x)). Qed.
Lemma lem5713954 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713955 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term36 _119721 op x) = (term396 _119721 op x).
Proof. exact (MK_COMB (@lem5713954 _119721) (@lem5713953 _119721 op x)). Qed.
Lemma lem5713956 {_119721 : Type'} (op : type1400 _119721) : (term37 _119721 op) = (term397 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5713955 _119721 op x)). Qed.
Lemma lem5713957 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5713958 {_119721 : Type'} (op : type1400 _119721) : (term38 _119721 op) = (term398 _119721 op).
Proof. exact (MK_COMB (@lem5713957 _119721) (@lem5713956 _119721 op)). Qed.
Lemma lem5713959 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5713960 {_119721 : Type'} (op : type1400 _119721) : (term39 _119721 op) = (term399 _119721 op).
Proof. exact (MK_COMB (@lem5713959) (@lem5713958 _119721 op)). Qed.
Lemma lem5713961 {_119721 : Type'} (op : type1400 _119721) : (term1 _119721 op) = (term400 _119721 op).
Proof. exact (MK_COMB (@lem5713960 _119721 op) (@lem5713915 _119721 op)). Qed.
Lemma lem5713962 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term400 _119721 op.
Proof. exact (EQ_MP (@lem5713961 _119721 op) (@lem5713306 _119721 op h1)). Qed.
Lemma lem5713963 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5713964 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5713973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713974 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713973 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713975 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (op b) = (@I (_119721 -> _119721 -> _119721) op b).
Proof. exact (@lem5713974 _119721 op b). Qed.
Lemma lem5713976 {_119721 : Type'} (c : _119721) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5713977 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (op b c) = (@I (_119721 -> _119721 -> _119721) op b c).
Proof. exact (MK_COMB (@lem5713975 _119721 op b) (@lem5713976 _119721 c)). Qed.
Lemma lem5713979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713980 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713979 _119721 _119721 f x). Qed.
Lemma lem5713981 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (@I (_119721 -> _119721 -> _119721) op b c) = (term373 _119721 op b c).
Proof. exact (@lem5713980 _119721 (@I (_119721 -> _119721 -> _119721) op b) c). Qed.
Lemma lem5713983 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (op b c) = (term373 _119721 op b c).
Proof. exact (TRANS (@lem5713977 _119721 op b c) (@lem5713981 _119721 op b c)). Qed.
Lemma lem5713984 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (op a).
Proof. exact (eq_refl (op a)). Qed.
Lemma lem5713985 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term19 _119721 a op b c) = (term374 _119721 a op b c).
Proof. exact (MK_COMB (@lem5713984 _119721 op a) (@lem5713983 _119721 op b c)). Qed.
Lemma lem5713987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713988 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5713987 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5713989 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (@I (_119721 -> _119721 -> _119721) op a).
Proof. exact (@lem5713988 _119721 op a). Qed.
Lemma lem5713990 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (term373 _119721 op b c) = (term373 _119721 op b c).
Proof. exact (eq_refl (term373 _119721 op b c)). Qed.
Lemma lem5713991 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term374 _119721 a op b c) = (term375 _119721 a op b c).
Proof. exact (MK_COMB (@lem5713989 _119721 op a) (@lem5713990 _119721 op b c)). Qed.
Lemma lem5713993 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5713994 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5713993 _119721 _119721 f x). Qed.
Lemma lem5713995 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term375 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (@lem5713994 _119721 (@I (_119721 -> _119721 -> _119721) op a) (term373 _119721 op b c)). Qed.
Lemma lem5713996 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term374 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (TRANS (@lem5713991 _119721 a op b c) (@lem5713995 _119721 a op b c)). Qed.
Lemma lem5713997 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term19 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (TRANS (@lem5713985 _119721 a op b c) (@lem5713996 _119721 a op b c)). Qed.
Lemma lem5714006 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714007 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714006 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714008 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (@I (_119721 -> _119721 -> _119721) op a).
Proof. exact (@lem5714007 _119721 op a). Qed.
Lemma lem5714009 {_119721 : Type'} (c : _119721) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5714010 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (c : _119721) : (op a c) = (@I (_119721 -> _119721 -> _119721) op a c).
Proof. exact (MK_COMB (@lem5714008 _119721 op a) (@lem5714009 _119721 c)). Qed.
Lemma lem5714012 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714013 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714012 _119721 _119721 f x). Qed.
Lemma lem5714014 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (c : _119721) : (@I (_119721 -> _119721 -> _119721) op a c) = (term373 _119721 op a c).
Proof. exact (@lem5714013 _119721 (@I (_119721 -> _119721 -> _119721) op a) c). Qed.
Lemma lem5714016 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (c : _119721) : (op a c) = (term373 _119721 op a c).
Proof. exact (TRANS (@lem5714010 _119721 op a c) (@lem5714014 _119721 op a c)). Qed.
Lemma lem5714017 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (op b) = (op b).
Proof. exact (eq_refl (op b)). Qed.
Lemma lem5714018 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term19 _119721 b op a c) = (term374 _119721 b op a c).
Proof. exact (MK_COMB (@lem5714017 _119721 op b) (@lem5714016 _119721 op a c)). Qed.
Lemma lem5714020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714021 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714020 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714022 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (op b) = (@I (_119721 -> _119721 -> _119721) op b).
Proof. exact (@lem5714021 _119721 op b). Qed.
Lemma lem5714023 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (c : _119721) : (term373 _119721 op a c) = (term373 _119721 op a c).
Proof. exact (eq_refl (term373 _119721 op a c)). Qed.
Lemma lem5714024 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term374 _119721 b op a c) = (term375 _119721 b op a c).
Proof. exact (MK_COMB (@lem5714022 _119721 op b) (@lem5714023 _119721 op a c)). Qed.
Lemma lem5714026 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714027 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714026 _119721 _119721 f x). Qed.
Lemma lem5714028 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term375 _119721 b op a c) = (term376 _119721 b op a c).
Proof. exact (@lem5714027 _119721 (@I (_119721 -> _119721 -> _119721) op b) (term373 _119721 op a c)). Qed.
Lemma lem5714029 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term374 _119721 b op a c) = (term376 _119721 b op a c).
Proof. exact (TRANS (@lem5714024 _119721 b op a c) (@lem5714028 _119721 b op a c)). Qed.
Lemma lem5714030 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term19 _119721 b op a c) = (term376 _119721 b op a c).
Proof. exact (TRANS (@lem5714018 _119721 b op a c) (@lem5714029 _119721 b op a c)). Qed.
Lemma lem5714031 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term383 _119721 a op b c) = (term384 _119721 a op b c).
Proof. exact (MK_COMB (@lem5713964 _119721) (@lem5713997 _119721 a op b c)). Qed.
Lemma lem5714032 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : ((term19 _119721 a op b c) = (term19 _119721 b op a c)) = ((term376 _119721 a op b c) = (term376 _119721 b op a c)).
Proof. exact (MK_COMB (@lem5714031 _119721 a op b c) (@lem5714030 _119721 b op a c)). Qed.
Lemma lem5714033 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term119 _119721 b op a c) = (term401 _119721 b op a c).
Proof. exact (MK_COMB (@lem5713963) (@lem5714032 _119721 b op a c)). Qed.
Lemma lem5714034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5714035 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5714036 {_119721 : Type'} (op : type1400 _119721) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem5714043 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714044 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714043 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714045 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (@I (_119721 -> _119721 -> _119721) op a).
Proof. exact (@lem5714044 _119721 op a). Qed.
Lemma lem5714046 {_119721 : Type'} (b : _119721) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5714047 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (op a b) = (@I (_119721 -> _119721 -> _119721) op a b).
Proof. exact (MK_COMB (@lem5714045 _119721 op a) (@lem5714046 _119721 b)). Qed.
Lemma lem5714049 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714050 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714049 _119721 _119721 f x). Qed.
Lemma lem5714051 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (@I (_119721 -> _119721 -> _119721) op a b) = (term373 _119721 op a b).
Proof. exact (@lem5714050 _119721 (@I (_119721 -> _119721 -> _119721) op a) b). Qed.
Lemma lem5714053 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (op a b) = (term373 _119721 op a b).
Proof. exact (TRANS (@lem5714047 _119721 op a b) (@lem5714051 _119721 op a b)). Qed.
Lemma lem5714054 {_119721 : Type'} (c : _119721) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5714055 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (term377 _119721 op a b) = (term378 _119721 op a b).
Proof. exact (MK_COMB (@lem5714036 _119721 op) (@lem5714053 _119721 op a b)). Qed.
Lemma lem5714056 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) (c : _119721) : (term26 _119721 op a b c) = (term379 _119721 op a b c).
Proof. exact (MK_COMB (@lem5714055 _119721 op a b) (@lem5714054 _119721 c)). Qed.
Lemma lem5714058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714059 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714058 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714060 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (term378 _119721 op a b) = (term380 _119721 op a b).
Proof. exact (@lem5714059 _119721 op (term373 _119721 op a b)). Qed.
Lemma lem5714061 {_119721 : Type'} (c : _119721) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5714062 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) (c : _119721) : (term379 _119721 op a b c) = (term381 _119721 op a b c).
Proof. exact (MK_COMB (@lem5714060 _119721 op a b) (@lem5714061 _119721 c)). Qed.
Lemma lem5714064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714065 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714064 _119721 _119721 f x). Qed.
Lemma lem5714066 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) (c : _119721) : (term381 _119721 op a b c) = (term382 _119721 op a b c).
Proof. exact (@lem5714065 _119721 (term380 _119721 op a b) c). Qed.
Lemma lem5714067 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) (c : _119721) : (term379 _119721 op a b c) = (term382 _119721 op a b c).
Proof. exact (TRANS (@lem5714062 _119721 op a b c) (@lem5714066 _119721 op a b c)). Qed.
Lemma lem5714068 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) (c : _119721) : (term26 _119721 op a b c) = (term382 _119721 op a b c).
Proof. exact (TRANS (@lem5714056 _119721 op a b c) (@lem5714067 _119721 op a b c)). Qed.
Lemma lem5714077 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714078 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714077 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714079 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (op b) = (@I (_119721 -> _119721 -> _119721) op b).
Proof. exact (@lem5714078 _119721 op b). Qed.
Lemma lem5714080 {_119721 : Type'} (c : _119721) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5714081 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (op b c) = (@I (_119721 -> _119721 -> _119721) op b c).
Proof. exact (MK_COMB (@lem5714079 _119721 op b) (@lem5714080 _119721 c)). Qed.
Lemma lem5714083 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714084 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714083 _119721 _119721 f x). Qed.
Lemma lem5714085 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (@I (_119721 -> _119721 -> _119721) op b c) = (term373 _119721 op b c).
Proof. exact (@lem5714084 _119721 (@I (_119721 -> _119721 -> _119721) op b) c). Qed.
Lemma lem5714087 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (op b c) = (term373 _119721 op b c).
Proof. exact (TRANS (@lem5714081 _119721 op b c) (@lem5714085 _119721 op b c)). Qed.
Lemma lem5714088 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (op a).
Proof. exact (eq_refl (op a)). Qed.
Lemma lem5714089 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term19 _119721 a op b c) = (term374 _119721 a op b c).
Proof. exact (MK_COMB (@lem5714088 _119721 op a) (@lem5714087 _119721 op b c)). Qed.
Lemma lem5714091 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714092 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714091 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714093 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (@I (_119721 -> _119721 -> _119721) op a).
Proof. exact (@lem5714092 _119721 op a). Qed.
Lemma lem5714094 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) : (term373 _119721 op b c) = (term373 _119721 op b c).
Proof. exact (eq_refl (term373 _119721 op b c)). Qed.
Lemma lem5714095 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term374 _119721 a op b c) = (term375 _119721 a op b c).
Proof. exact (MK_COMB (@lem5714093 _119721 op a) (@lem5714094 _119721 op b c)). Qed.
Lemma lem5714097 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714098 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714097 _119721 _119721 f x). Qed.
Lemma lem5714099 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term375 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (@lem5714098 _119721 (@I (_119721 -> _119721 -> _119721) op a) (term373 _119721 op b c)). Qed.
Lemma lem5714100 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term374 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (TRANS (@lem5714095 _119721 a op b c) (@lem5714099 _119721 a op b c)). Qed.
Lemma lem5714101 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term19 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (TRANS (@lem5714089 _119721 a op b c) (@lem5714100 _119721 a op b c)). Qed.
Lemma lem5714102 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) (c : _119721) : (term402 _119721 op a b c) = (term403 _119721 op a b c).
Proof. exact (MK_COMB (@lem5714035 _119721) (@lem5714068 _119721 op a b c)). Qed.
Lemma lem5714103 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : ((term26 _119721 op a b c) = (term19 _119721 a op b c)) = ((term382 _119721 op a b c) = (term376 _119721 a op b c)).
Proof. exact (MK_COMB (@lem5714102 _119721 op a b c) (@lem5714101 _119721 a op b c)). Qed.
Lemma lem5714104 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term97 _119721 a op b c) = (term404 _119721 a op b c).
Proof. exact (MK_COMB (@lem5714034) (@lem5714103 _119721 a op b c)). Qed.
Lemma lem5714105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5714106 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term206 _119721 a op b c) = (term405 _119721 a op b c).
Proof. exact (MK_COMB (@lem5714105) (@lem5714104 _119721 a op b c)). Qed.
Lemma lem5714107 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term208 _119721 b op a c) = (term406 _119721 b op a c).
Proof. exact (MK_COMB (@lem5714106 _119721 a op b c) (@lem5714033 _119721 b op a c)). Qed.
Lemma lem5714108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5714109 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5714116 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714117 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714116 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714118 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (@I (_119721 -> _119721 -> _119721) op a).
Proof. exact (@lem5714117 _119721 op a). Qed.
Lemma lem5714119 {_119721 : Type'} (b : _119721) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5714120 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (op a b) = (@I (_119721 -> _119721 -> _119721) op a b).
Proof. exact (MK_COMB (@lem5714118 _119721 op a) (@lem5714119 _119721 b)). Qed.
Lemma lem5714122 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714123 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714122 _119721 _119721 f x). Qed.
Lemma lem5714124 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (@I (_119721 -> _119721 -> _119721) op a b) = (term373 _119721 op a b).
Proof. exact (@lem5714123 _119721 (@I (_119721 -> _119721 -> _119721) op a) b). Qed.
Lemma lem5714126 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (op a b) = (term373 _119721 op a b).
Proof. exact (TRANS (@lem5714120 _119721 op a b) (@lem5714124 _119721 op a b)). Qed.
Lemma lem5714133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714134 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714133 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714135 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (op b) = (@I (_119721 -> _119721 -> _119721) op b).
Proof. exact (@lem5714134 _119721 op b). Qed.
Lemma lem5714136 {_119721 : Type'} (a : _119721) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5714137 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (op b a) = (@I (_119721 -> _119721 -> _119721) op b a).
Proof. exact (MK_COMB (@lem5714135 _119721 op b) (@lem5714136 _119721 a)). Qed.
Lemma lem5714139 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714140 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714139 _119721 _119721 f x). Qed.
Lemma lem5714141 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (@I (_119721 -> _119721 -> _119721) op b a) = (term373 _119721 op b a).
Proof. exact (@lem5714140 _119721 (@I (_119721 -> _119721 -> _119721) op b) a). Qed.
Lemma lem5714143 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (op b a) = (term373 _119721 op b a).
Proof. exact (TRANS (@lem5714137 _119721 op b a) (@lem5714141 _119721 op b a)). Qed.
Lemma lem5714144 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) : (term393 _119721 op a b) = (term394 _119721 op a b).
Proof. exact (MK_COMB (@lem5714109 _119721) (@lem5714126 _119721 op a b)). Qed.
Lemma lem5714145 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : ((op a b) = (op b a)) = ((term373 _119721 op a b) = (term373 _119721 op b a)).
Proof. exact (MK_COMB (@lem5714144 _119721 op a b) (@lem5714143 _119721 op b a)). Qed.
Lemma lem5714146 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term82 _119721 op b a) = (term407 _119721 op b a).
Proof. exact (MK_COMB (@lem5714108) (@lem5714145 _119721 op b a)). Qed.
Lemma lem5714147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5714148 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term247 _119721 op b a) = (term408 _119721 op b a).
Proof. exact (MK_COMB (@lem5714147) (@lem5714146 _119721 op b a)). Qed.
Lemma lem5714149 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term263 _119721 b op a c) = (term409 _119721 b op a c).
Proof. exact (MK_COMB (@lem5714148 _119721 op b a) (@lem5714107 _119721 b op a c)). Qed.
Lemma lem5714150 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5714151 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5714160 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714161 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714160 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714162 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (op a) = (@I (_119721 -> _119721 -> _119721) op a).
Proof. exact (@lem5714161 _119721 op a). Qed.
Lemma lem5714163 {_119721 : Type'} (op : type1400 _119721) : (@neutral _119721 op) = (@neutral _119721 op).
Proof. exact (eq_refl (@neutral _119721 op)). Qed.
Lemma lem5714164 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term41 _119721 a op) = (term410 _119721 a op).
Proof. exact (MK_COMB (@lem5714162 _119721 op a) (@lem5714163 _119721 op)). Qed.
Lemma lem5714166 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714167 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714166 _119721 _119721 f x). Qed.
Lemma lem5714168 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term410 _119721 a op) = (term411 _119721 a op).
Proof. exact (@lem5714167 _119721 (@I (_119721 -> _119721 -> _119721) op a) (@neutral _119721 op)). Qed.
Lemma lem5714170 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term41 _119721 a op) = (term411 _119721 a op).
Proof. exact (TRANS (@lem5714164 _119721 a op) (@lem5714168 _119721 a op)). Qed.
Lemma lem5714171 {_119721 : Type'} (a : _119721) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5714172 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term412 _119721 a op) = (term413 _119721 a op).
Proof. exact (MK_COMB (@lem5714151 _119721) (@lem5714170 _119721 a op)). Qed.
Lemma lem5714173 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term41 _119721 a op) = a) = ((term411 _119721 a op) = a).
Proof. exact (MK_COMB (@lem5714172 _119721 a op) (@lem5714171 _119721 a)). Qed.
Lemma lem5714174 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term74 _119721 op a) = (term414 _119721 op a).
Proof. exact (MK_COMB (@lem5714150) (@lem5714173 _119721 op a)). Qed.
Lemma lem5714175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5714176 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term284 _119721 op a) = (term415 _119721 op a).
Proof. exact (MK_COMB (@lem5714175) (@lem5714174 _119721 op a)). Qed.
Lemma lem5714177 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term310 _119721 b op a c) = (term416 _119721 b op a c).
Proof. exact (MK_COMB (@lem5714176 _119721 op a) (@lem5714149 _119721 b op a c)). Qed.
Lemma lem5714178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5714179 {_119721 : Type'} : (@eq _119721) = (@eq _119721).
Proof. exact (eq_refl (@eq _119721)). Qed.
Lemma lem5714188 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714189 {_119721 : Type'} (f : type1400 _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721 -> _119721) f x).
Proof. exact (@lem5714188 _119721 (_119721 -> _119721) f x). Qed.
Lemma lem5714190 {_119721 : Type'} (op : type1400 _119721) : (term365 _119721 op) = (term366 _119721 op).
Proof. exact (@lem5714189 _119721 op (@neutral _119721 op)). Qed.
Lemma lem5714191 {_119721 : Type'} (a : _119721) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5714192 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term46 _119721 op a) = (term367 _119721 op a).
Proof. exact (MK_COMB (@lem5714190 _119721 op) (@lem5714191 _119721 a)). Qed.
Lemma lem5714194 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5714195 {_119721 : Type'} (f : _119721 -> _119721) (x : _119721) : (f x) = (@I (_119721 -> _119721) f x).
Proof. exact (@lem5714194 _119721 _119721 f x). Qed.
Lemma lem5714196 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term367 _119721 op a) = (term368 _119721 op a).
Proof. exact (@lem5714195 _119721 (term366 _119721 op) a). Qed.
Lemma lem5714198 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term46 _119721 op a) = (term368 _119721 op a).
Proof. exact (TRANS (@lem5714192 _119721 op a) (@lem5714196 _119721 op a)). Qed.
Lemma lem5714199 {_119721 : Type'} (a : _119721) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5714200 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term369 _119721 op a) = (term370 _119721 op a).
Proof. exact (MK_COMB (@lem5714179 _119721) (@lem5714198 _119721 op a)). Qed.
Lemma lem5714201 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : ((term46 _119721 op a) = a) = ((term368 _119721 op a) = a).
Proof. exact (MK_COMB (@lem5714200 _119721 op a) (@lem5714199 _119721 a)). Qed.
Lemma lem5714202 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term66 _119721 op a) = (term417 _119721 op a).
Proof. exact (MK_COMB (@lem5714178) (@lem5714201 _119721 op a)). Qed.
Lemma lem5714203 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5714204 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term331 _119721 op a) = (term418 _119721 op a).
Proof. exact (MK_COMB (@lem5714203) (@lem5714202 _119721 op a)). Qed.
Lemma lem5714205 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term357 _119721 b op a c) = (term419 _119721 b op a c).
Proof. exact (MK_COMB (@lem5714204 _119721 op a) (@lem5714177 _119721 b op a c)). Qed.
Lemma lem5714206 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term357 _119721 b op a c) : term419 _119721 b op a c.
Proof. exact (EQ_MP (@lem5714205 _119721 b op a c) (@lem5713808 _119721 b op a c h1)). Qed.
Lemma lem5714207 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term392 _119721 op.
Proof. exact (proj2 (@lem5713962 _119721 op h1)). Qed.
Lemma lem5714208 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term398 _119721 op.
Proof. exact (proj1 (@lem5713962 _119721 op h1)). Qed.
Lemma lem5714209 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term372 _119721 op.
Proof. exact (proj2 (@lem5714207 _119721 op h1)). Qed.
Lemma lem5714210 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term390 _119721 op.
Proof. exact (proj1 (@lem5714207 _119721 op h1)). Qed.
Lemma lem5714212 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term416 _119721 b op a c) : term416 _119721 b op a c.
Proof. exact (h1). Qed.
Lemma lem5714214 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term409 _119721 b op a c) : term409 _119721 b op a c.
Proof. exact (h1). Qed.
Lemma lem5714216 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term406 _119721 b op a c) : term406 _119721 b op a c.
Proof. exact (h1). Qed.
Lemma lem5714243 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : ((term368 _119721 op x) = x) = ((term368 _119721 op x) = x).
Proof. exact (eq_refl ((term368 _119721 op x) = x)). Qed.
Lemma lem5714244 {_119721 : Type'} (op : type1400 _119721) : (term371 _119721 op) = (term371 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5714243 _119721 op x)). Qed.
Lemma lem5714245 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714247 {_119721 : Type'} (op : type1400 _119721) : (term372 _119721 op) = (term372 _119721 op).
Proof. exact (MK_COMB (@lem5714245 _119721) (@lem5714244 _119721 op)). Qed.
Lemma lem5714248 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term372 _119721 op.
Proof. exact (EQ_MP (@lem5714247 _119721 op) (@lem5714209 _119721 op h1)). Qed.
Lemma lem5714252 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (h1 : term417 _119721 op a) : term417 _119721 op a.
Proof. exact (h1). Qed.
Lemma lem5714254 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : ((term373 _119721 op x y) = (term373 _119721 op y x)) = ((term373 _119721 op x y) = (term373 _119721 op y x)).
Proof. exact (eq_refl ((term373 _119721 op x y) = (term373 _119721 op y x))). Qed.
Lemma lem5714255 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term395 _119721 op x) = (term395 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5714254 _119721 op y x)). Qed.
Lemma lem5714256 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714257 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term396 _119721 op x) = (term396 _119721 op x).
Proof. exact (MK_COMB (@lem5714256 _119721) (@lem5714255 _119721 op x)). Qed.
Lemma lem5714258 {_119721 : Type'} (op : type1400 _119721) : (term397 _119721 op) = (term397 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5714257 _119721 op x)). Qed.
Lemma lem5714259 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714261 {_119721 : Type'} (op : type1400 _119721) : (term398 _119721 op) = (term398 _119721 op).
Proof. exact (MK_COMB (@lem5714259 _119721) (@lem5714258 _119721 op)). Qed.
Lemma lem5714262 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term398 _119721 op.
Proof. exact (EQ_MP (@lem5714261 _119721 op) (@lem5714208 _119721 op h1)). Qed.
Lemma lem5714277 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : ((term368 _119721 op x) = x) = ((term368 _119721 op x) = x).
Proof. exact (eq_refl ((term368 _119721 op x) = x)). Qed.
Lemma lem5714278 {_119721 : Type'} (op : type1400 _119721) : (term371 _119721 op) = (term371 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5714277 _119721 op x)). Qed.
Lemma lem5714279 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714281 {_119721 : Type'} (op : type1400 _119721) : (term372 _119721 op) = (term372 _119721 op).
Proof. exact (MK_COMB (@lem5714279 _119721) (@lem5714278 _119721 op)). Qed.
Lemma lem5714282 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term372 _119721 op.
Proof. exact (EQ_MP (@lem5714281 _119721 op) (@lem5714209 _119721 op h1)). Qed.
Lemma lem5714286 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (h1 : term414 _119721 op a) : term414 _119721 op a.
Proof. exact (h1). Qed.
Lemma lem5714288 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : ((term373 _119721 op x y) = (term373 _119721 op y x)) = ((term373 _119721 op x y) = (term373 _119721 op y x)).
Proof. exact (eq_refl ((term373 _119721 op x y) = (term373 _119721 op y x))). Qed.
Lemma lem5714289 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term395 _119721 op x) = (term395 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5714288 _119721 op y x)). Qed.
Lemma lem5714290 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714291 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term396 _119721 op x) = (term396 _119721 op x).
Proof. exact (MK_COMB (@lem5714290 _119721) (@lem5714289 _119721 op x)). Qed.
Lemma lem5714292 {_119721 : Type'} (op : type1400 _119721) : (term397 _119721 op) = (term397 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5714291 _119721 op x)). Qed.
Lemma lem5714293 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714295 {_119721 : Type'} (op : type1400 _119721) : (term398 _119721 op) = (term398 _119721 op).
Proof. exact (MK_COMB (@lem5714293 _119721) (@lem5714292 _119721 op)). Qed.
Lemma lem5714296 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term398 _119721 op.
Proof. exact (EQ_MP (@lem5714295 _119721 op) (@lem5714208 _119721 op h1)). Qed.
Lemma lem5714320 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) (h1 : term407 _119721 op b a) : term407 _119721 op b a.
Proof. exact (h1). Qed.
Lemma lem5714332 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : ((term376 _119721 x op y z) = (term382 _119721 op x y z)) = ((term376 _119721 x op y z) = (term382 _119721 op x y z)).
Proof. exact (eq_refl ((term376 _119721 x op y z) = (term382 _119721 op x y z))). Qed.
Lemma lem5714333 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term385 _119721 op x y) = (term385 _119721 op x y).
Proof. exact (fun_ext (fun z : _119721 => @lem5714332 _119721 op x y z)). Qed.
Lemma lem5714334 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714335 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term386 _119721 op x y) = (term386 _119721 op x y).
Proof. exact (MK_COMB (@lem5714334 _119721) (@lem5714333 _119721 op x y)). Qed.
Lemma lem5714336 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term387 _119721 op x) = (term387 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5714335 _119721 op x y)). Qed.
Lemma lem5714337 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714338 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term388 _119721 op x) = (term388 _119721 op x).
Proof. exact (MK_COMB (@lem5714337 _119721) (@lem5714336 _119721 op x)). Qed.
Lemma lem5714339 {_119721 : Type'} (op : type1400 _119721) : (term389 _119721 op) = (term389 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5714338 _119721 op x)). Qed.
Lemma lem5714340 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714342 {_119721 : Type'} (op : type1400 _119721) : (term390 _119721 op) = (term390 _119721 op).
Proof. exact (MK_COMB (@lem5714340 _119721) (@lem5714339 _119721 op)). Qed.
Lemma lem5714343 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term390 _119721 op.
Proof. exact (EQ_MP (@lem5714342 _119721 op) (@lem5714210 _119721 op h1)). Qed.
Lemma lem5714354 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) (h1 : term404 _119721 a op b c) : term404 _119721 a op b c.
Proof. exact (h1). Qed.
Lemma lem5714356 {_119721 : Type'} (op : type1400 _119721) (y : _119721) (x : _119721) : ((term373 _119721 op x y) = (term373 _119721 op y x)) = ((term373 _119721 op x y) = (term373 _119721 op y x)).
Proof. exact (eq_refl ((term373 _119721 op x y) = (term373 _119721 op y x))). Qed.
Lemma lem5714357 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term395 _119721 op x) = (term395 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5714356 _119721 op y x)). Qed.
Lemma lem5714358 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714359 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term396 _119721 op x) = (term396 _119721 op x).
Proof. exact (MK_COMB (@lem5714358 _119721) (@lem5714357 _119721 op x)). Qed.
Lemma lem5714360 {_119721 : Type'} (op : type1400 _119721) : (term397 _119721 op) = (term397 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5714359 _119721 op x)). Qed.
Lemma lem5714361 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714363 {_119721 : Type'} (op : type1400 _119721) : (term398 _119721 op) = (term398 _119721 op).
Proof. exact (MK_COMB (@lem5714361 _119721) (@lem5714360 _119721 op)). Qed.
Lemma lem5714364 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term398 _119721 op.
Proof. exact (EQ_MP (@lem5714363 _119721 op) (@lem5714208 _119721 op h1)). Qed.
Lemma lem5714366 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) (z : _119721) : ((term376 _119721 x op y z) = (term382 _119721 op x y z)) = ((term376 _119721 x op y z) = (term382 _119721 op x y z)).
Proof. exact (eq_refl ((term376 _119721 x op y z) = (term382 _119721 op x y z))). Qed.
Lemma lem5714367 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term385 _119721 op x y) = (term385 _119721 op x y).
Proof. exact (fun_ext (fun z : _119721 => @lem5714366 _119721 op x y z)). Qed.
Lemma lem5714368 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714369 {_119721 : Type'} (op : type1400 _119721) (x : _119721) (y : _119721) : (term386 _119721 op x y) = (term386 _119721 op x y).
Proof. exact (MK_COMB (@lem5714368 _119721) (@lem5714367 _119721 op x y)). Qed.
Lemma lem5714370 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term387 _119721 op x) = (term387 _119721 op x).
Proof. exact (fun_ext (fun y : _119721 => @lem5714369 _119721 op x y)). Qed.
Lemma lem5714371 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714372 {_119721 : Type'} (op : type1400 _119721) (x : _119721) : (term388 _119721 op x) = (term388 _119721 op x).
Proof. exact (MK_COMB (@lem5714371 _119721) (@lem5714370 _119721 op x)). Qed.
Lemma lem5714373 {_119721 : Type'} (op : type1400 _119721) : (term389 _119721 op) = (term389 _119721 op).
Proof. exact (fun_ext (fun x : _119721 => @lem5714372 _119721 op x)). Qed.
Lemma lem5714374 {_119721 : Type'} : (@all _119721) = (@all _119721).
Proof. exact (eq_refl (@all _119721)). Qed.
Lemma lem5714376 {_119721 : Type'} (op : type1400 _119721) : (term390 _119721 op) = (term390 _119721 op).
Proof. exact (MK_COMB (@lem5714374 _119721) (@lem5714373 _119721 op)). Qed.
Lemma lem5714377 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term390 _119721 op.
Proof. exact (EQ_MP (@lem5714376 _119721 op) (@lem5714210 _119721 op h1)). Qed.
Lemma lem5714388 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term401 _119721 b op a c) : term401 _119721 b op a c.
Proof. exact (h1). Qed.
Lemma lem5714404 {_119721 : Type'} (_71619 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term420 _119721 op _71619.
Proof. exact (@lem5714248 _119721 op h1 _71619). Qed.
Lemma lem5714405 {_119721 : Type'} (op : type1400 _119721) (_71619 : _119721) : (term420 _119721 op _71619) = ((term368 _119721 op _71619) = _71619).
Proof. exact (eq_refl (term420 _119721 op _71619)). Qed.
Lemma lem5714407 {_119721 : Type'} (_71620 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term421 _119721 op _71620.
Proof. exact (@lem5714262 _119721 op h1 _71620). Qed.
Lemma lem5714408 {_119721 : Type'} (op : type1400 _119721) (_71620 : _119721) : (term421 _119721 op _71620) = (term396 _119721 op _71620).
Proof. exact (eq_refl (term421 _119721 op _71620)). Qed.
Lemma lem5714409 {_119721 : Type'} (_71620 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term396 _119721 op _71620.
Proof. exact (EQ_MP (@lem5714408 _119721 op _71620) (@lem5714407 _119721 _71620 op h1)). Qed.
Lemma lem5714410 {_119721 : Type'} (_71620 : _119721) (_71621 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term422 _119721 op _71620 _71621.
Proof. exact (@lem5714409 _119721 _71620 op h1 _71621). Qed.
Lemma lem5714411 {_119721 : Type'} (op : type1400 _119721) (_71621 : _119721) (_71620 : _119721) : (term422 _119721 op _71620 _71621) = ((term373 _119721 op _71620 _71621) = (term373 _119721 op _71621 _71620)).
Proof. exact (eq_refl (term422 _119721 op _71620 _71621)). Qed.
Lemma lem5714422 {_119721 : Type'} (_71625 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term420 _119721 op _71625.
Proof. exact (@lem5714282 _119721 op h1 _71625). Qed.
Lemma lem5714423 {_119721 : Type'} (op : type1400 _119721) (_71625 : _119721) : (term420 _119721 op _71625) = ((term368 _119721 op _71625) = _71625).
Proof. exact (eq_refl (term420 _119721 op _71625)). Qed.
Lemma lem5714425 {_119721 : Type'} (_71626 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term421 _119721 op _71626.
Proof. exact (@lem5714296 _119721 op h1 _71626). Qed.
Lemma lem5714426 {_119721 : Type'} (op : type1400 _119721) (_71626 : _119721) : (term421 _119721 op _71626) = (term396 _119721 op _71626).
Proof. exact (eq_refl (term421 _119721 op _71626)). Qed.
Lemma lem5714427 {_119721 : Type'} (_71626 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term396 _119721 op _71626.
Proof. exact (EQ_MP (@lem5714426 _119721 op _71626) (@lem5714425 _119721 _71626 op h1)). Qed.
Lemma lem5714428 {_119721 : Type'} (_71626 : _119721) (_71627 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term422 _119721 op _71626 _71627.
Proof. exact (@lem5714427 _119721 _71626 op h1 _71627). Qed.
Lemma lem5714429 {_119721 : Type'} (op : type1400 _119721) (_71627 : _119721) (_71626 : _119721) : (term422 _119721 op _71626 _71627) = ((term373 _119721 op _71626 _71627) = (term373 _119721 op _71627 _71626)).
Proof. exact (eq_refl (term422 _119721 op _71626 _71627)). Qed.
Lemma lem5714449 {_119721 : Type'} (_71634 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term423 _119721 op _71634.
Proof. exact (@lem5714343 _119721 op h1 _71634). Qed.
Lemma lem5714450 {_119721 : Type'} (op : type1400 _119721) (_71634 : _119721) : (term423 _119721 op _71634) = (term388 _119721 op _71634).
Proof. exact (eq_refl (term423 _119721 op _71634)). Qed.
Lemma lem5714451 {_119721 : Type'} (_71634 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term388 _119721 op _71634.
Proof. exact (EQ_MP (@lem5714450 _119721 op _71634) (@lem5714449 _119721 _71634 op h1)). Qed.
Lemma lem5714452 {_119721 : Type'} (_71634 : _119721) (_71635 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term424 _119721 op _71634 _71635.
Proof. exact (@lem5714451 _119721 _71634 op h1 _71635). Qed.
Lemma lem5714453 {_119721 : Type'} (op : type1400 _119721) (_71634 : _119721) (_71635 : _119721) : (term424 _119721 op _71634 _71635) = (term386 _119721 op _71634 _71635).
Proof. exact (eq_refl (term424 _119721 op _71634 _71635)). Qed.
Lemma lem5714454 {_119721 : Type'} (_71634 : _119721) (_71635 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term386 _119721 op _71634 _71635.
Proof. exact (EQ_MP (@lem5714453 _119721 op _71634 _71635) (@lem5714452 _119721 _71634 _71635 op h1)). Qed.
Lemma lem5714455 {_119721 : Type'} (_71634 : _119721) (_71635 : _119721) (_71636 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term425 _119721 op _71634 _71635 _71636.
Proof. exact (@lem5714454 _119721 _71634 _71635 op h1 _71636). Qed.
Lemma lem5714456 {_119721 : Type'} (op : type1400 _119721) (_71634 : _119721) (_71635 : _119721) (_71636 : _119721) : (term425 _119721 op _71634 _71635 _71636) = ((term376 _119721 _71634 op _71635 _71636) = (term382 _119721 op _71634 _71635 _71636)).
Proof. exact (eq_refl (term425 _119721 op _71634 _71635 _71636)). Qed.
Lemma lem5714461 {_119721 : Type'} (_71638 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term421 _119721 op _71638.
Proof. exact (@lem5714364 _119721 op h1 _71638). Qed.
Lemma lem5714462 {_119721 : Type'} (op : type1400 _119721) (_71638 : _119721) : (term421 _119721 op _71638) = (term396 _119721 op _71638).
Proof. exact (eq_refl (term421 _119721 op _71638)). Qed.
Lemma lem5714463 {_119721 : Type'} (_71638 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term396 _119721 op _71638.
Proof. exact (EQ_MP (@lem5714462 _119721 op _71638) (@lem5714461 _119721 _71638 op h1)). Qed.
Lemma lem5714464 {_119721 : Type'} (_71638 : _119721) (_71639 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term422 _119721 op _71638 _71639.
Proof. exact (@lem5714463 _119721 _71638 op h1 _71639). Qed.
Lemma lem5714465 {_119721 : Type'} (op : type1400 _119721) (_71639 : _119721) (_71638 : _119721) : (term422 _119721 op _71638 _71639) = ((term373 _119721 op _71638 _71639) = (term373 _119721 op _71639 _71638)).
Proof. exact (eq_refl (term422 _119721 op _71638 _71639)). Qed.
Lemma lem5714467 {_119721 : Type'} (_71640 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term423 _119721 op _71640.
Proof. exact (@lem5714377 _119721 op h1 _71640). Qed.
Lemma lem5714468 {_119721 : Type'} (op : type1400 _119721) (_71640 : _119721) : (term423 _119721 op _71640) = (term388 _119721 op _71640).
Proof. exact (eq_refl (term423 _119721 op _71640)). Qed.
Lemma lem5714469 {_119721 : Type'} (_71640 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term388 _119721 op _71640.
Proof. exact (EQ_MP (@lem5714468 _119721 op _71640) (@lem5714467 _119721 _71640 op h1)). Qed.
Lemma lem5714470 {_119721 : Type'} (_71640 : _119721) (_71641 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term424 _119721 op _71640 _71641.
Proof. exact (@lem5714469 _119721 _71640 op h1 _71641). Qed.
Lemma lem5714471 {_119721 : Type'} (op : type1400 _119721) (_71640 : _119721) (_71641 : _119721) : (term424 _119721 op _71640 _71641) = (term386 _119721 op _71640 _71641).
Proof. exact (eq_refl (term424 _119721 op _71640 _71641)). Qed.
Lemma lem5714472 {_119721 : Type'} (_71640 : _119721) (_71641 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term386 _119721 op _71640 _71641.
Proof. exact (EQ_MP (@lem5714471 _119721 op _71640 _71641) (@lem5714470 _119721 _71640 _71641 op h1)). Qed.
Lemma lem5714473 {_119721 : Type'} (_71640 : _119721) (_71641 : _119721) (_71642 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term425 _119721 op _71640 _71641 _71642.
Proof. exact (@lem5714472 _119721 _71640 _71641 op h1 _71642). Qed.
Lemma lem5714474 {_119721 : Type'} (op : type1400 _119721) (_71640 : _119721) (_71641 : _119721) (_71642 : _119721) : (term425 _119721 op _71640 _71641 _71642) = ((term376 _119721 _71640 op _71641 _71642) = (term382 _119721 op _71640 _71641 _71642)).
Proof. exact (eq_refl (term425 _119721 op _71640 _71641 _71642)). Qed.
Lemma lem5714486 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (h1 : term417 _119721 op a) : term417 _119721 op a.
Proof. exact (h1). Qed.
Lemma lem5714494 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (h1 : term414 _119721 op a) : term414 _119721 op a.
Proof. exact (h1). Qed.
Lemma lem5714502 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) (h1 : term407 _119721 op b a) : term407 _119721 op b a.
Proof. exact (h1). Qed.
Lemma lem5714510 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) (h1 : term404 _119721 a op b c) : term404 _119721 a op b c.
Proof. exact (h1). Qed.
Lemma lem5714518 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term401 _119721 b op a c) : term401 _119721 b op a c.
Proof. exact (h1). Qed.
Lemma lem5714564 {_119721 : Type'} (_71619 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op _71619) = _71619.
Proof. exact (EQ_MP (@lem5714405 _119721 op _71619) (@lem5714404 _119721 _71619 op h1)). Qed.
Lemma lem5714565 {_119721 : Type'} (_71619 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op _71619) = _71619.
Proof. exact (@lem5714564 _119721 _71619 op h1). Qed.
Lemma lem5714566 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op a) = a.
Proof. exact (@lem5714565 _119721 a op h1). Qed.
Lemma lem5714567 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term426 _119721 op a.
Proof. exact (fun h0 : term417 _119721 op a => @lem5714566 _119721 a op h1). Qed.
Lemma lem5714569 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714570 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term426 _119721 op a) = ((term368 _119721 op a) = a).
Proof. exact (@lem5714569 ((term368 _119721 op a) = a)). Qed.
Lemma lem5714571 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op a) = a.
Proof. exact (EQ_MP (@lem5714570 _119721 op a) (@lem5714567 _119721 a op h1)). Qed.
Lemma lem5714574 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5714576 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term417 _119721 op a) = (term428 _119721 op a).
Proof. exact (@lem5714574 ((term368 _119721 op a) = a)). Qed.
Lemma lem5714579 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (h1 : term417 _119721 op a) : term428 _119721 op a.
Proof. exact (EQ_MP (@lem5714576 _119721 op a) (@lem5714486 _119721 op a h1)). Qed.
Lemma lem5714582 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (@lem5714579 _119721 op a h1 (@lem5714571 _119721 a op h2)). Qed.
Lemma lem5714583 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : term429.
Proof. exact (fun h0 : ~ False => @lem5714582 _119721 a op h1 h2). Qed.
Lemma lem5714585 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714586 : term429 = False.
Proof. exact (@lem5714585 False). Qed.
Lemma lem5714587 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5714586) (@lem5714583 _119721 a op h1 h2)). Qed.
Lemma lem5714627 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term430 _119721 x y z.
Proof. exact (@lem21385 _119721 x y z). Qed.
Lemma lem5714633 {_119721 : Type'} (_71621 : _119721) (_71620 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71620 _71621) = (term373 _119721 op _71621 _71620).
Proof. exact (EQ_MP (@lem5714411 _119721 op _71621 _71620) (@lem5714410 _119721 _71620 _71621 op h1)). Qed.
Lemma lem5714634 {_119721 : Type'} (_71621 : _119721) (_71620 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71620 _71621) = (term373 _119721 op _71621 _71620).
Proof. exact (@lem5714633 _119721 _71621 _71620 op h1). Qed.
Lemma lem5714635 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op a) = (term411 _119721 a op).
Proof. exact (@lem5714634 _119721 a (@neutral _119721 op) op h1). Qed.
Lemma lem5714636 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term431 _119721 a op.
Proof. exact (fun h0 : term432 _119721 a op => @lem5714635 _119721 a op h1). Qed.
Lemma lem5714638 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714639 {_119721 : Type'} (a : _119721) (op : type1400 _119721) : (term431 _119721 a op) = ((term368 _119721 op a) = (term411 _119721 a op)).
Proof. exact (@lem5714638 ((term368 _119721 op a) = (term411 _119721 a op))). Qed.
Lemma lem5714640 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op a) = (term411 _119721 a op).
Proof. exact (EQ_MP (@lem5714639 _119721 a op) (@lem5714636 _119721 a op h1)). Qed.
Lemma lem5714642 {_119721 : Type'} (_71625 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op _71625) = _71625.
Proof. exact (EQ_MP (@lem5714423 _119721 op _71625) (@lem5714422 _119721 _71625 op h1)). Qed.
Lemma lem5714643 {_119721 : Type'} (_71625 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op _71625) = _71625.
Proof. exact (@lem5714642 _119721 _71625 op h1). Qed.
Lemma lem5714644 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op a) = a.
Proof. exact (@lem5714643 _119721 a op h1). Qed.
Lemma lem5714645 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term426 _119721 op a.
Proof. exact (fun h0 : term417 _119721 op a => @lem5714644 _119721 a op h1). Qed.
Lemma lem5714647 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714648 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term426 _119721 op a) = ((term368 _119721 op a) = a).
Proof. exact (@lem5714647 ((term368 _119721 op a) = a)). Qed.
Lemma lem5714649 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term368 _119721 op a) = a.
Proof. exact (EQ_MP (@lem5714648 _119721 op a) (@lem5714645 _119721 a op h1)). Qed.
Lemma lem5714667 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5714668 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term433 _119721 x y z) = (term434 _119721 y x z).
Proof. exact (@lem5714667 (y = z) (term435 _119721 x z)). Qed.
Lemma lem5714678 {_119721 : Type'} (x : _119721) (y : _119721) : (term436 _119721 x y) = (term436 _119721 x y).
Proof. exact (eq_refl (term436 _119721 x y)). Qed.
Lemma lem5714679 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term437 _119721 y x z).
Proof. exact (MK_COMB (@lem5714678 _119721 x y) (@lem5714668 _119721 y x z)). Qed.
Lemma lem5714683 (q : Prop) (p : Prop) (r : Prop) : (term438 p q r) = (term438 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5714684 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term437 _119721 y x z) = (term439 _119721 y x z).
Proof. exact (@lem5714683 (y = z) (term435 _119721 x y) (term435 _119721 x z)). Qed.
Lemma lem5714706 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term439 _119721 y x z).
Proof. exact (TRANS (@lem5714679 _119721 y x z) (@lem5714684 _119721 y x z)). Qed.
Lemma lem5714707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5714708 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term440 _119721 x y z) = (term441 _119721 y x z).
Proof. exact (MK_COMB (@lem5714707) (@lem5714706 _119721 y x z)). Qed.
Lemma lem5714730 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term439 _119721 y x z) = (term439 _119721 y x z).
Proof. exact (eq_refl (term439 _119721 y x z)). Qed.
Lemma lem5714731 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term430 _119721 x y z) = (term439 _119721 y x z)) = ((term439 _119721 y x z) = (term439 _119721 y x z)).
Proof. exact (MK_COMB (@lem5714708 _119721 y x z) (@lem5714730 _119721 y x z)). Qed.
Lemma lem5714733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5714734 (x : Prop) : (x = x) = True.
Proof. exact (@lem5714733 Prop x). Qed.
Lemma lem5714735 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term439 _119721 y x z) = (term439 _119721 y x z)) = True.
Proof. exact (@lem5714734 (term439 _119721 y x z)). Qed.
Lemma lem5714736 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term430 _119721 x y z) = (term439 _119721 y x z)) = True.
Proof. exact (TRANS (@lem5714731 _119721 y x z) (@lem5714735 _119721 y x z)). Qed.
Lemma lem5714737 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : True = ((term430 _119721 x y z) = (term439 _119721 y x z)).
Proof. exact (SYM (@lem5714736 _119721 y x z)). Qed.
Lemma lem5714738 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term439 _119721 y x z).
Proof. exact (EQ_MP (@lem5714737 _119721 y x z) (@lem0)). Qed.
Lemma lem5714739 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : term439 _119721 y x z.
Proof. exact (EQ_MP (@lem5714738 _119721 y x z) (@lem5714627 _119721 x y z)). Qed.
Lemma lem5714741 (b : Prop) (a : Prop) : (a \/ b) = (term442 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5714742 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term439 _119721 y x z) = (term443 _119721 x y z).
Proof. exact (@lem5714741 (term444 _119721 y x z) (y = z)). Qed.
Lemma lem5714744 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5714745 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term447 _119721 y x z) = (term448 _119721 y x z).
Proof. exact (@lem5714744 (term435 _119721 x y) (term435 _119721 x z)). Qed.
Lemma lem5714747 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5714748 {_119721 : Type'} (x : _119721) (y : _119721) : (term449 _119721 x y) = (x = y).
Proof. exact (@lem5714747 (x = y)). Qed.
Lemma lem5714749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5714750 {_119721 : Type'} (x : _119721) (y : _119721) : (term450 _119721 x y) = (term451 _119721 x y).
Proof. exact (MK_COMB (@lem5714749) (@lem5714748 _119721 x y)). Qed.
Lemma lem5714752 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5714753 {_119721 : Type'} (x : _119721) (z : _119721) : (term449 _119721 x z) = (x = z).
Proof. exact (@lem5714752 (x = z)). Qed.
Lemma lem5714754 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term448 _119721 y x z) = (term452 _119721 y x z).
Proof. exact (MK_COMB (@lem5714750 _119721 x y) (@lem5714753 _119721 x z)). Qed.
Lemma lem5714755 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term447 _119721 y x z) = (term452 _119721 y x z).
Proof. exact (TRANS (@lem5714745 _119721 y x z) (@lem5714754 _119721 y x z)). Qed.
Lemma lem5714756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5714757 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term453 _119721 y x z) = (term454 _119721 y x z).
Proof. exact (MK_COMB (@lem5714756) (@lem5714755 _119721 y x z)). Qed.
Lemma lem5714758 {_119721 : Type'} (y : _119721) (z : _119721) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5714759 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term443 _119721 x y z) = (term455 _119721 x y z).
Proof. exact (MK_COMB (@lem5714757 _119721 y x z) (@lem5714758 _119721 y z)). Qed.
Lemma lem5714760 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term439 _119721 y x z) = (term455 _119721 x y z).
Proof. exact (TRANS (@lem5714742 _119721 x y z) (@lem5714759 _119721 x y z)). Qed.
Lemma lem5714762 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term456 _119721 op a.
Proof. exact (conj (@lem5714640 _119721 a op h1) (@lem5714649 _119721 a op h1)). Qed.
Lemma lem5714764 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (EQ_MP (@lem5714760 _119721 x y z) (@lem5714739 _119721 y x z)). Qed.
Lemma lem5714765 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (@lem5714764 _119721 x y z). Qed.
Lemma lem5714766 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : term457 _119721 op a.
Proof. exact (@lem5714765 _119721 (term368 _119721 op a) (term411 _119721 a op) a). Qed.
Lemma lem5714769 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term411 _119721 a op) = a.
Proof. exact (@lem5714766 _119721 op a (@lem5714762 _119721 a op h1)). Qed.
Lemma lem5714770 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term411 _119721 a op) = a.
Proof. exact (@lem5714769 _119721 a op h1). Qed.
Lemma lem5714771 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term458 _119721 op a.
Proof. exact (fun h0 : term414 _119721 op a => @lem5714770 _119721 a op h1). Qed.
Lemma lem5714773 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714774 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term458 _119721 op a) = ((term411 _119721 a op) = a).
Proof. exact (@lem5714773 ((term411 _119721 a op) = a)). Qed.
Lemma lem5714775 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term411 _119721 a op) = a.
Proof. exact (EQ_MP (@lem5714774 _119721 op a) (@lem5714771 _119721 a op h1)). Qed.
Lemma lem5714778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5714780 {_119721 : Type'} (op : type1400 _119721) (a : _119721) : (term414 _119721 op a) = (term459 _119721 op a).
Proof. exact (@lem5714778 ((term411 _119721 a op) = a)). Qed.
Lemma lem5714783 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (h1 : term414 _119721 op a) : term459 _119721 op a.
Proof. exact (EQ_MP (@lem5714780 _119721 op a) (@lem5714494 _119721 op a h1)). Qed.
Lemma lem5714786 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (@lem5714783 _119721 op a h1 (@lem5714775 _119721 a op h2)). Qed.
Lemma lem5714787 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : term429.
Proof. exact (fun h0 : ~ False => @lem5714786 _119721 a op h1 h2). Qed.
Lemma lem5714789 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714790 : term429 = False.
Proof. exact (@lem5714789 False). Qed.
Lemma lem5714791 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5714790) (@lem5714787 _119721 a op h1 h2)). Qed.
Lemma lem5714837 {_119721 : Type'} (_71627 : _119721) (_71626 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71626 _71627) = (term373 _119721 op _71627 _71626).
Proof. exact (EQ_MP (@lem5714429 _119721 op _71627 _71626) (@lem5714428 _119721 _71626 _71627 op h1)). Qed.
Lemma lem5714838 {_119721 : Type'} (_71627 : _119721) (_71626 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71626 _71627) = (term373 _119721 op _71627 _71626).
Proof. exact (@lem5714837 _119721 _71627 _71626 op h1). Qed.
Lemma lem5714839 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op a b) = (term373 _119721 op b a).
Proof. exact (@lem5714838 _119721 b a op h1). Qed.
Lemma lem5714840 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term460 _119721 op b a.
Proof. exact (fun h0 : term407 _119721 op b a => @lem5714839 _119721 b a op h1). Qed.
Lemma lem5714842 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714843 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term460 _119721 op b a) = ((term373 _119721 op a b) = (term373 _119721 op b a)).
Proof. exact (@lem5714842 ((term373 _119721 op a b) = (term373 _119721 op b a))). Qed.
Lemma lem5714844 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op a b) = (term373 _119721 op b a).
Proof. exact (EQ_MP (@lem5714843 _119721 op b a) (@lem5714840 _119721 b a op h1)). Qed.
Lemma lem5714847 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5714849 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) : (term407 _119721 op b a) = (term461 _119721 op b a).
Proof. exact (@lem5714847 ((term373 _119721 op a b) = (term373 _119721 op b a))). Qed.
Lemma lem5714852 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (a : _119721) (h1 : term407 _119721 op b a) : term461 _119721 op b a.
Proof. exact (EQ_MP (@lem5714849 _119721 op b a) (@lem5714502 _119721 op b a h1)). Qed.
Lemma lem5714855 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : False.
Proof. exact (@lem5714852 _119721 op b a h1 (@lem5714844 _119721 b a op h2)). Qed.
Lemma lem5714856 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : term429.
Proof. exact (fun h0 : ~ False => @lem5714855 _119721 b a op h1 h2). Qed.
Lemma lem5714858 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714859 : term429 = False.
Proof. exact (@lem5714858 False). Qed.
Lemma lem5714860 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5714859) (@lem5714856 _119721 b a op h1 h2)). Qed.
Lemma lem5714900 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term430 _119721 x y z.
Proof. exact (@lem21385 _119721 x y z). Qed.
Lemma lem5714906 {_119721 : Type'} (_71634 : _119721) (_71635 : _119721) (_71636 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 _71634 op _71635 _71636) = (term382 _119721 op _71634 _71635 _71636).
Proof. exact (EQ_MP (@lem5714456 _119721 op _71634 _71635 _71636) (@lem5714455 _119721 _71634 _71635 _71636 op h1)). Qed.
Lemma lem5714907 {_119721 : Type'} (_71634 : _119721) (_71635 : _119721) (_71636 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 _71634 op _71635 _71636) = (term382 _119721 op _71634 _71635 _71636).
Proof. exact (@lem5714906 _119721 _71634 _71635 _71636 op h1). Qed.
Lemma lem5714908 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 a op b c) = (term382 _119721 op a b c).
Proof. exact (@lem5714907 _119721 a b c op h1). Qed.
Lemma lem5714909 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term462 _119721 op a b c.
Proof. exact (fun h0 : term463 _119721 op a b c => @lem5714908 _119721 a b c op h1). Qed.
Lemma lem5714911 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714912 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (b : _119721) (c : _119721) : (term462 _119721 op a b c) = ((term376 _119721 a op b c) = (term382 _119721 op a b c)).
Proof. exact (@lem5714911 ((term376 _119721 a op b c) = (term382 _119721 op a b c))). Qed.
Lemma lem5714913 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 a op b c) = (term382 _119721 op a b c).
Proof. exact (EQ_MP (@lem5714912 _119721 op a b c) (@lem5714909 _119721 a b c op h1)). Qed.
Lemma lem5714915 {_119721 : Type'} (x : _119721) : x = x.
Proof. exact (@lem21386 _119721 x). Qed.
Lemma lem5714916 {_119721 : Type'} (x : _119721) : x = x.
Proof. exact (@lem5714915 _119721 x). Qed.
Lemma lem5714917 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term376 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (@lem5714916 _119721 (term376 _119721 a op b c)). Qed.
Lemma lem5714918 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : term464 _119721 a op b c.
Proof. exact (fun h0 : term465 _119721 a op b c => @lem5714917 _119721 a op b c). Qed.
Lemma lem5714920 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5714921 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term464 _119721 a op b c) = ((term376 _119721 a op b c) = (term376 _119721 a op b c)).
Proof. exact (@lem5714920 ((term376 _119721 a op b c) = (term376 _119721 a op b c))). Qed.
Lemma lem5714922 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term376 _119721 a op b c) = (term376 _119721 a op b c).
Proof. exact (EQ_MP (@lem5714921 _119721 a op b c) (@lem5714918 _119721 a op b c)). Qed.
Lemma lem5714940 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5714941 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term433 _119721 x y z) = (term434 _119721 y x z).
Proof. exact (@lem5714940 (y = z) (term435 _119721 x z)). Qed.
Lemma lem5714951 {_119721 : Type'} (x : _119721) (y : _119721) : (term436 _119721 x y) = (term436 _119721 x y).
Proof. exact (eq_refl (term436 _119721 x y)). Qed.
Lemma lem5714952 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term437 _119721 y x z).
Proof. exact (MK_COMB (@lem5714951 _119721 x y) (@lem5714941 _119721 y x z)). Qed.
Lemma lem5714956 (q : Prop) (p : Prop) (r : Prop) : (term438 p q r) = (term438 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5714957 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term437 _119721 y x z) = (term439 _119721 y x z).
Proof. exact (@lem5714956 (y = z) (term435 _119721 x y) (term435 _119721 x z)). Qed.
Lemma lem5714979 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term439 _119721 y x z).
Proof. exact (TRANS (@lem5714952 _119721 y x z) (@lem5714957 _119721 y x z)). Qed.
Lemma lem5714980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5714981 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term440 _119721 x y z) = (term441 _119721 y x z).
Proof. exact (MK_COMB (@lem5714980) (@lem5714979 _119721 y x z)). Qed.
Lemma lem5715003 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term439 _119721 y x z) = (term439 _119721 y x z).
Proof. exact (eq_refl (term439 _119721 y x z)). Qed.
Lemma lem5715004 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term430 _119721 x y z) = (term439 _119721 y x z)) = ((term439 _119721 y x z) = (term439 _119721 y x z)).
Proof. exact (MK_COMB (@lem5714981 _119721 y x z) (@lem5715003 _119721 y x z)). Qed.
Lemma lem5715006 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5715007 (x : Prop) : (x = x) = True.
Proof. exact (@lem5715006 Prop x). Qed.
Lemma lem5715008 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term439 _119721 y x z) = (term439 _119721 y x z)) = True.
Proof. exact (@lem5715007 (term439 _119721 y x z)). Qed.
Lemma lem5715009 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term430 _119721 x y z) = (term439 _119721 y x z)) = True.
Proof. exact (TRANS (@lem5715004 _119721 y x z) (@lem5715008 _119721 y x z)). Qed.
Lemma lem5715010 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : True = ((term430 _119721 x y z) = (term439 _119721 y x z)).
Proof. exact (SYM (@lem5715009 _119721 y x z)). Qed.
Lemma lem5715011 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term439 _119721 y x z).
Proof. exact (EQ_MP (@lem5715010 _119721 y x z) (@lem0)). Qed.
Lemma lem5715012 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : term439 _119721 y x z.
Proof. exact (EQ_MP (@lem5715011 _119721 y x z) (@lem5714900 _119721 x y z)). Qed.
Lemma lem5715014 (b : Prop) (a : Prop) : (a \/ b) = (term442 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5715015 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term439 _119721 y x z) = (term443 _119721 x y z).
Proof. exact (@lem5715014 (term444 _119721 y x z) (y = z)). Qed.
Lemma lem5715017 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5715018 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term447 _119721 y x z) = (term448 _119721 y x z).
Proof. exact (@lem5715017 (term435 _119721 x y) (term435 _119721 x z)). Qed.
Lemma lem5715020 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5715021 {_119721 : Type'} (x : _119721) (y : _119721) : (term449 _119721 x y) = (x = y).
Proof. exact (@lem5715020 (x = y)). Qed.
Lemma lem5715022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5715023 {_119721 : Type'} (x : _119721) (y : _119721) : (term450 _119721 x y) = (term451 _119721 x y).
Proof. exact (MK_COMB (@lem5715022) (@lem5715021 _119721 x y)). Qed.
Lemma lem5715025 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5715026 {_119721 : Type'} (x : _119721) (z : _119721) : (term449 _119721 x z) = (x = z).
Proof. exact (@lem5715025 (x = z)). Qed.
Lemma lem5715027 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term448 _119721 y x z) = (term452 _119721 y x z).
Proof. exact (MK_COMB (@lem5715023 _119721 x y) (@lem5715026 _119721 x z)). Qed.
Lemma lem5715028 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term447 _119721 y x z) = (term452 _119721 y x z).
Proof. exact (TRANS (@lem5715018 _119721 y x z) (@lem5715027 _119721 y x z)). Qed.
Lemma lem5715029 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5715030 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term453 _119721 y x z) = (term454 _119721 y x z).
Proof. exact (MK_COMB (@lem5715029) (@lem5715028 _119721 y x z)). Qed.
Lemma lem5715031 {_119721 : Type'} (y : _119721) (z : _119721) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5715032 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term443 _119721 x y z) = (term455 _119721 x y z).
Proof. exact (MK_COMB (@lem5715030 _119721 y x z) (@lem5715031 _119721 y z)). Qed.
Lemma lem5715033 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term439 _119721 y x z) = (term455 _119721 x y z).
Proof. exact (TRANS (@lem5715015 _119721 x y z) (@lem5715032 _119721 x y z)). Qed.
Lemma lem5715035 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term466 _119721 a op b c.
Proof. exact (conj (@lem5714913 _119721 a b c op h1) (@lem5714922 _119721 a op b c)). Qed.
Lemma lem5715037 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (EQ_MP (@lem5715033 _119721 x y z) (@lem5715012 _119721 y x z)). Qed.
Lemma lem5715038 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (@lem5715037 _119721 x y z). Qed.
Lemma lem5715039 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : term467 _119721 a op b c.
Proof. exact (@lem5715038 _119721 (term376 _119721 a op b c) (term382 _119721 op a b c) (term376 _119721 a op b c)). Qed.
Lemma lem5715042 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op a b c) = (term376 _119721 a op b c).
Proof. exact (@lem5715039 _119721 a op b c (@lem5715035 _119721 a b c op h1)). Qed.
Lemma lem5715043 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op a b c) = (term376 _119721 a op b c).
Proof. exact (@lem5715042 _119721 a b c op h1). Qed.
Lemma lem5715044 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term468 _119721 a op b c.
Proof. exact (fun h0 : term404 _119721 a op b c => @lem5715043 _119721 a b c op h1). Qed.
Lemma lem5715046 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715047 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term468 _119721 a op b c) = ((term382 _119721 op a b c) = (term376 _119721 a op b c)).
Proof. exact (@lem5715046 ((term382 _119721 op a b c) = (term376 _119721 a op b c))). Qed.
Lemma lem5715048 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op a b c) = (term376 _119721 a op b c).
Proof. exact (EQ_MP (@lem5715047 _119721 a op b c) (@lem5715044 _119721 a b c op h1)). Qed.
Lemma lem5715051 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5715053 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term404 _119721 a op b c) = (term469 _119721 a op b c).
Proof. exact (@lem5715051 ((term382 _119721 op a b c) = (term376 _119721 a op b c))). Qed.
Lemma lem5715056 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) (h1 : term404 _119721 a op b c) : term469 _119721 a op b c.
Proof. exact (EQ_MP (@lem5715053 _119721 a op b c) (@lem5714510 _119721 a op b c h1)). Qed.
Lemma lem5715059 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : False.
Proof. exact (@lem5715056 _119721 a op b c h1 (@lem5715048 _119721 a b c op h2)). Qed.
Lemma lem5715060 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : term429.
Proof. exact (fun h0 : ~ False => @lem5715059 _119721 a b c op h1 h2). Qed.
Lemma lem5715062 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715063 : term429 = False.
Proof. exact (@lem5715062 False). Qed.
Lemma lem5715064 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715063) (@lem5715060 _119721 a b c op h1 h2)). Qed.
Lemma lem5715088 {_119721 : Type'} : (@I (_119721 -> _119721)) = (@I (_119721 -> _119721)).
Proof. exact (eq_refl (@I (_119721 -> _119721))). Qed.
Lemma lem5715089 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) (h1 : _71690 = _71692) : _71690 = _71692.
Proof. exact (h1). Qed.
Lemma lem5715090 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (h1 : _71691 = _71693) : _71691 = _71693.
Proof. exact (h1). Qed.
Lemma lem5715091 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) (h1 : _71690 = _71692) : (@I (_119721 -> _119721) _71690) = (@I (_119721 -> _119721) _71692).
Proof. exact (MK_COMB (@lem5715088 _119721) (@lem5715089 _119721 _71690 _71692 h1)). Qed.
Lemma lem5715092 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) (h1 : _71691 = _71693) (h2 : _71690 = _71692) : (@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693).
Proof. exact (MK_COMB (@lem5715091 _119721 _71690 _71692 h2) (@lem5715090 _119721 _71691 _71693 h1)). Qed.
Lemma lem5715093 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) (_71691 : _119721) (_71693 : _119721) (h1 : _71691 = _71693) : term470 _119721 _71690 _71691 _71692 _71693.
Proof. exact (fun h0 : _71690 = _71692 => @lem5715092 _119721 _71691 _71693 _71690 _71692 h1 h0). Qed.
Lemma lem5715095 (a : Prop) (b : Prop) : (a -> b) = (term471 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5715096 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : (term470 _119721 _71690 _71691 _71692 _71693) = (term472 _119721 _71690 _71691 _71692 _71693).
Proof. exact (@lem5715095 (_71690 = _71692) ((@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693))). Qed.
Lemma lem5715097 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) (_71691 : _119721) (_71693 : _119721) (h1 : _71691 = _71693) : term472 _119721 _71690 _71691 _71692 _71693.
Proof. exact (EQ_MP (@lem5715096 _119721 _71690 _71691 _71692 _71693) (@lem5715093 _119721 _71690 _71692 _71691 _71693 h1)). Qed.
Lemma lem5715098 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : term473 _119721 _71690 _71691 _71692 _71693.
Proof. exact (fun h0 : _71691 = _71693 => @lem5715097 _119721 _71690 _71692 _71691 _71693 h0). Qed.
Lemma lem5715100 (a : Prop) (b : Prop) : (a -> b) = (term471 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5715101 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : (term473 _119721 _71690 _71691 _71692 _71693) = (term474 _119721 _71690 _71691 _71692 _71693).
Proof. exact (@lem5715100 (_71691 = _71693) (term472 _119721 _71690 _71691 _71692 _71693)). Qed.
Lemma lem5715102 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : term474 _119721 _71690 _71691 _71692 _71693.
Proof. exact (EQ_MP (@lem5715101 _119721 _71690 _71691 _71692 _71693) (@lem5715098 _119721 _71690 _71691 _71692 _71693)). Qed.
Lemma lem5715104 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term430 _119721 x y z.
Proof. exact (@lem21385 _119721 x y z). Qed.
Lemma lem5715110 {_119721 : Type'} (_71639 : _119721) (_71638 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71638 _71639) = (term373 _119721 op _71639 _71638).
Proof. exact (EQ_MP (@lem5714465 _119721 op _71639 _71638) (@lem5714464 _119721 _71638 _71639 op h1)). Qed.
Lemma lem5715111 {_119721 : Type'} (_71639 : _119721) (_71638 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71638 _71639) = (term373 _119721 op _71639 _71638).
Proof. exact (@lem5715110 _119721 _71639 _71638 op h1). Qed.
Lemma lem5715112 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op b c a) = (term376 _119721 a op b c).
Proof. exact (@lem5715111 _119721 a (term373 _119721 op b c) op h1). Qed.
Lemma lem5715113 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term475 _119721 a op b c.
Proof. exact (fun h0 : term476 _119721 a op b c => @lem5715112 _119721 a b c op h1). Qed.
Lemma lem5715115 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715116 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (b : _119721) (c : _119721) : (term475 _119721 a op b c) = ((term382 _119721 op b c a) = (term376 _119721 a op b c)).
Proof. exact (@lem5715115 ((term382 _119721 op b c a) = (term376 _119721 a op b c))). Qed.
Lemma lem5715117 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op b c a) = (term376 _119721 a op b c).
Proof. exact (EQ_MP (@lem5715116 _119721 a op b c) (@lem5715113 _119721 a b c op h1)). Qed.
Lemma lem5715119 {_119721 : Type'} (_71640 : _119721) (_71641 : _119721) (_71642 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 _71640 op _71641 _71642) = (term382 _119721 op _71640 _71641 _71642).
Proof. exact (EQ_MP (@lem5714474 _119721 op _71640 _71641 _71642) (@lem5714473 _119721 _71640 _71641 _71642 op h1)). Qed.
Lemma lem5715120 {_119721 : Type'} (_71640 : _119721) (_71641 : _119721) (_71642 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 _71640 op _71641 _71642) = (term382 _119721 op _71640 _71641 _71642).
Proof. exact (@lem5715119 _119721 _71640 _71641 _71642 op h1). Qed.
Lemma lem5715121 {_119721 : Type'} (b : _119721) (c : _119721) (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 b op c a) = (term382 _119721 op b c a).
Proof. exact (@lem5715120 _119721 b c a op h1). Qed.
Lemma lem5715122 {_119721 : Type'} (b : _119721) (c : _119721) (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term462 _119721 op b c a.
Proof. exact (fun h0 : term463 _119721 op b c a => @lem5715121 _119721 b c a op h1). Qed.
Lemma lem5715124 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715125 {_119721 : Type'} (op : type1400 _119721) (b : _119721) (c : _119721) (a : _119721) : (term462 _119721 op b c a) = ((term376 _119721 b op c a) = (term382 _119721 op b c a)).
Proof. exact (@lem5715124 ((term376 _119721 b op c a) = (term382 _119721 op b c a))). Qed.
Lemma lem5715126 {_119721 : Type'} (b : _119721) (c : _119721) (a : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 b op c a) = (term382 _119721 op b c a).
Proof. exact (EQ_MP (@lem5715125 _119721 op b c a) (@lem5715122 _119721 b c a op h1)). Qed.
Lemma lem5715128 {_119721 : Type'} (_71639 : _119721) (_71638 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71638 _71639) = (term373 _119721 op _71639 _71638).
Proof. exact (EQ_MP (@lem5714465 _119721 op _71639 _71638) (@lem5714464 _119721 _71638 _71639 op h1)). Qed.
Lemma lem5715129 {_119721 : Type'} (_71639 : _119721) (_71638 : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op _71638 _71639) = (term373 _119721 op _71639 _71638).
Proof. exact (@lem5715128 _119721 _71639 _71638 op h1). Qed.
Lemma lem5715130 {_119721 : Type'} (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op c a) = (term373 _119721 op a c).
Proof. exact (@lem5715129 _119721 a c op h1). Qed.
Lemma lem5715131 {_119721 : Type'} (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term460 _119721 op a c.
Proof. exact (fun h0 : term407 _119721 op a c => @lem5715130 _119721 a c op h1). Qed.
Lemma lem5715133 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715134 {_119721 : Type'} (op : type1400 _119721) (a : _119721) (c : _119721) : (term460 _119721 op a c) = ((term373 _119721 op c a) = (term373 _119721 op a c)).
Proof. exact (@lem5715133 ((term373 _119721 op c a) = (term373 _119721 op a c))). Qed.
Lemma lem5715135 {_119721 : Type'} (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term373 _119721 op c a) = (term373 _119721 op a c).
Proof. exact (EQ_MP (@lem5715134 _119721 op a c) (@lem5715131 _119721 a c op h1)). Qed.
Lemma lem5715137 {_119721 : Type'} (x : _119721 -> _119721) : x = x.
Proof. exact (@lem21386 (_119721 -> _119721) x). Qed.
Lemma lem5715138 {_119721 : Type'} (x : _119721 -> _119721) : x = x.
Proof. exact (@lem5715137 _119721 x). Qed.
Lemma lem5715139 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (@I (_119721 -> _119721 -> _119721) op b) = (@I (_119721 -> _119721 -> _119721) op b).
Proof. exact (@lem5715138 _119721 (@I (_119721 -> _119721 -> _119721) op b)). Qed.
Lemma lem5715140 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : term477 _119721 op b.
Proof. exact (fun h0 : term478 _119721 op b => @lem5715139 _119721 op b). Qed.
Lemma lem5715142 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715143 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (term477 _119721 op b) = ((@I (_119721 -> _119721 -> _119721) op b) = (@I (_119721 -> _119721 -> _119721) op b)).
Proof. exact (@lem5715142 ((@I (_119721 -> _119721 -> _119721) op b) = (@I (_119721 -> _119721 -> _119721) op b))). Qed.
Lemma lem5715144 {_119721 : Type'} (op : type1400 _119721) (b : _119721) : (@I (_119721 -> _119721 -> _119721) op b) = (@I (_119721 -> _119721 -> _119721) op b).
Proof. exact (EQ_MP (@lem5715143 _119721 op b) (@lem5715140 _119721 op b)). Qed.
Lemma lem5715162 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5715163 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term472 _119721 _71690 _71691 _71692 _71693) = (term479 _119721 _71691 _71693 _71690 _71692).
Proof. exact (@lem5715162 ((@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693)) (term480 _119721 _71690 _71692)). Qed.
Lemma lem5715173 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) : (term436 _119721 _71691 _71693) = (term436 _119721 _71691 _71693).
Proof. exact (eq_refl (term436 _119721 _71691 _71693)). Qed.
Lemma lem5715174 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term474 _119721 _71690 _71691 _71692 _71693) = (term481 _119721 _71691 _71693 _71690 _71692).
Proof. exact (MK_COMB (@lem5715173 _119721 _71691 _71693) (@lem5715163 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715178 (q : Prop) (p : Prop) (r : Prop) : (term438 p q r) = (term438 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5715179 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term481 _119721 _71691 _71693 _71690 _71692) = (term482 _119721 _71691 _71693 _71690 _71692).
Proof. exact (@lem5715178 ((@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693)) (term435 _119721 _71691 _71693) (term480 _119721 _71690 _71692)). Qed.
Lemma lem5715201 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term474 _119721 _71690 _71691 _71692 _71693) = (term482 _119721 _71691 _71693 _71690 _71692).
Proof. exact (TRANS (@lem5715174 _119721 _71691 _71693 _71690 _71692) (@lem5715179 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5715203 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term483 _119721 _71690 _71691 _71692 _71693) = (term484 _119721 _71691 _71693 _71690 _71692).
Proof. exact (MK_COMB (@lem5715202) (@lem5715201 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715225 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term482 _119721 _71691 _71693 _71690 _71692) = (term482 _119721 _71691 _71693 _71690 _71692).
Proof. exact (eq_refl (term482 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715226 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : ((term474 _119721 _71690 _71691 _71692 _71693) = (term482 _119721 _71691 _71693 _71690 _71692)) = ((term482 _119721 _71691 _71693 _71690 _71692) = (term482 _119721 _71691 _71693 _71690 _71692)).
Proof. exact (MK_COMB (@lem5715203 _119721 _71691 _71693 _71690 _71692) (@lem5715225 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715228 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5715229 (x : Prop) : (x = x) = True.
Proof. exact (@lem5715228 Prop x). Qed.
Lemma lem5715230 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : ((term482 _119721 _71691 _71693 _71690 _71692) = (term482 _119721 _71691 _71693 _71690 _71692)) = True.
Proof. exact (@lem5715229 (term482 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715231 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : ((term474 _119721 _71690 _71691 _71692 _71693) = (term482 _119721 _71691 _71693 _71690 _71692)) = True.
Proof. exact (TRANS (@lem5715226 _119721 _71691 _71693 _71690 _71692) (@lem5715230 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715232 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : True = ((term474 _119721 _71690 _71691 _71692 _71693) = (term482 _119721 _71691 _71693 _71690 _71692)).
Proof. exact (SYM (@lem5715231 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715233 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term474 _119721 _71690 _71691 _71692 _71693) = (term482 _119721 _71691 _71693 _71690 _71692).
Proof. exact (EQ_MP (@lem5715232 _119721 _71691 _71693 _71690 _71692) (@lem0)). Qed.
Lemma lem5715234 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : term482 _119721 _71691 _71693 _71690 _71692.
Proof. exact (EQ_MP (@lem5715233 _119721 _71691 _71693 _71690 _71692) (@lem5715102 _119721 _71690 _71691 _71692 _71693)). Qed.
Lemma lem5715236 (b : Prop) (a : Prop) : (a \/ b) = (term442 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5715237 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : (term482 _119721 _71691 _71693 _71690 _71692) = (term485 _119721 _71690 _71691 _71692 _71693).
Proof. exact (@lem5715236 (term486 _119721 _71691 _71693 _71690 _71692) ((@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693))). Qed.
Lemma lem5715239 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5715240 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term487 _119721 _71691 _71693 _71690 _71692) = (term488 _119721 _71691 _71693 _71690 _71692).
Proof. exact (@lem5715239 (term435 _119721 _71691 _71693) (term480 _119721 _71690 _71692)). Qed.
Lemma lem5715242 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5715243 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) : (term449 _119721 _71691 _71693) = (_71691 = _71693).
Proof. exact (@lem5715242 (_71691 = _71693)). Qed.
Lemma lem5715244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5715245 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) : (term450 _119721 _71691 _71693) = (term451 _119721 _71691 _71693).
Proof. exact (MK_COMB (@lem5715244) (@lem5715243 _119721 _71691 _71693)). Qed.
Lemma lem5715247 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5715248 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term489 _119721 _71690 _71692) = (_71690 = _71692).
Proof. exact (@lem5715247 (_71690 = _71692)). Qed.
Lemma lem5715249 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term488 _119721 _71691 _71693 _71690 _71692) = (term490 _119721 _71691 _71693 _71690 _71692).
Proof. exact (MK_COMB (@lem5715245 _119721 _71691 _71693) (@lem5715248 _119721 _71690 _71692)). Qed.
Lemma lem5715250 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term487 _119721 _71691 _71693 _71690 _71692) = (term490 _119721 _71691 _71693 _71690 _71692).
Proof. exact (TRANS (@lem5715240 _119721 _71691 _71693 _71690 _71692) (@lem5715249 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5715252 {_119721 : Type'} (_71691 : _119721) (_71693 : _119721) (_71690 : _119721 -> _119721) (_71692 : _119721 -> _119721) : (term491 _119721 _71691 _71693 _71690 _71692) = (term492 _119721 _71691 _71693 _71690 _71692).
Proof. exact (MK_COMB (@lem5715251) (@lem5715250 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715253 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : ((@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693)) = ((@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693)).
Proof. exact (eq_refl ((@I (_119721 -> _119721) _71690 _71691) = (@I (_119721 -> _119721) _71692 _71693))). Qed.
Lemma lem5715254 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : (term485 _119721 _71690 _71691 _71692 _71693) = (term493 _119721 _71690 _71691 _71692 _71693).
Proof. exact (MK_COMB (@lem5715252 _119721 _71691 _71693 _71690 _71692) (@lem5715253 _119721 _71690 _71691 _71692 _71693)). Qed.
Lemma lem5715255 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : (term482 _119721 _71691 _71693 _71690 _71692) = (term493 _119721 _71690 _71691 _71692 _71693).
Proof. exact (TRANS (@lem5715237 _119721 _71690 _71691 _71692 _71693) (@lem5715254 _119721 _71690 _71691 _71692 _71693)). Qed.
Lemma lem5715257 {_119721 : Type'} (a : _119721) (c : _119721) (b : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term494 _119721 a c op b.
Proof. exact (conj (@lem5715135 _119721 a c op h1) (@lem5715144 _119721 op b)). Qed.
Lemma lem5715259 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : term493 _119721 _71690 _71691 _71692 _71693.
Proof. exact (EQ_MP (@lem5715255 _119721 _71690 _71691 _71692 _71693) (@lem5715234 _119721 _71691 _71693 _71690 _71692)). Qed.
Lemma lem5715260 {_119721 : Type'} (_71690 : _119721 -> _119721) (_71691 : _119721) (_71692 : _119721 -> _119721) (_71693 : _119721) : term493 _119721 _71690 _71691 _71692 _71693.
Proof. exact (@lem5715259 _119721 _71690 _71691 _71692 _71693). Qed.
Lemma lem5715261 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : term495 _119721 b op a c.
Proof. exact (@lem5715260 _119721 (@I (_119721 -> _119721 -> _119721) op b) (term373 _119721 op c a) (@I (_119721 -> _119721 -> _119721) op b) (term373 _119721 op a c)). Qed.
Lemma lem5715264 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 b op c a) = (term376 _119721 b op a c).
Proof. exact (@lem5715261 _119721 b op a c (@lem5715257 _119721 a c b op h1)). Qed.
Lemma lem5715265 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 b op c a) = (term376 _119721 b op a c).
Proof. exact (@lem5715264 _119721 b a c op h1). Qed.
Lemma lem5715266 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term496 _119721 b op a c.
Proof. exact (fun h0 : term497 _119721 b op a c => @lem5715265 _119721 b a c op h1). Qed.
Lemma lem5715268 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715269 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term496 _119721 b op a c) = ((term376 _119721 b op c a) = (term376 _119721 b op a c)).
Proof. exact (@lem5715268 ((term376 _119721 b op c a) = (term376 _119721 b op a c))). Qed.
Lemma lem5715270 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 b op c a) = (term376 _119721 b op a c).
Proof. exact (EQ_MP (@lem5715269 _119721 b op a c) (@lem5715266 _119721 b a c op h1)). Qed.
Lemma lem5715288 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5715289 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term433 _119721 x y z) = (term434 _119721 y x z).
Proof. exact (@lem5715288 (y = z) (term435 _119721 x z)). Qed.
Lemma lem5715299 {_119721 : Type'} (x : _119721) (y : _119721) : (term436 _119721 x y) = (term436 _119721 x y).
Proof. exact (eq_refl (term436 _119721 x y)). Qed.
Lemma lem5715300 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term437 _119721 y x z).
Proof. exact (MK_COMB (@lem5715299 _119721 x y) (@lem5715289 _119721 y x z)). Qed.
Lemma lem5715304 (q : Prop) (p : Prop) (r : Prop) : (term438 p q r) = (term438 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5715305 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term437 _119721 y x z) = (term439 _119721 y x z).
Proof. exact (@lem5715304 (y = z) (term435 _119721 x y) (term435 _119721 x z)). Qed.
Lemma lem5715327 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term439 _119721 y x z).
Proof. exact (TRANS (@lem5715300 _119721 y x z) (@lem5715305 _119721 y x z)). Qed.
Lemma lem5715328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5715329 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term440 _119721 x y z) = (term441 _119721 y x z).
Proof. exact (MK_COMB (@lem5715328) (@lem5715327 _119721 y x z)). Qed.
Lemma lem5715351 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term439 _119721 y x z) = (term439 _119721 y x z).
Proof. exact (eq_refl (term439 _119721 y x z)). Qed.
Lemma lem5715352 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term430 _119721 x y z) = (term439 _119721 y x z)) = ((term439 _119721 y x z) = (term439 _119721 y x z)).
Proof. exact (MK_COMB (@lem5715329 _119721 y x z) (@lem5715351 _119721 y x z)). Qed.
Lemma lem5715354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5715355 (x : Prop) : (x = x) = True.
Proof. exact (@lem5715354 Prop x). Qed.
Lemma lem5715356 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term439 _119721 y x z) = (term439 _119721 y x z)) = True.
Proof. exact (@lem5715355 (term439 _119721 y x z)). Qed.
Lemma lem5715357 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : ((term430 _119721 x y z) = (term439 _119721 y x z)) = True.
Proof. exact (TRANS (@lem5715352 _119721 y x z) (@lem5715356 _119721 y x z)). Qed.
Lemma lem5715358 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : True = ((term430 _119721 x y z) = (term439 _119721 y x z)).
Proof. exact (SYM (@lem5715357 _119721 y x z)). Qed.
Lemma lem5715359 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term430 _119721 x y z) = (term439 _119721 y x z).
Proof. exact (EQ_MP (@lem5715358 _119721 y x z) (@lem0)). Qed.
Lemma lem5715360 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : term439 _119721 y x z.
Proof. exact (EQ_MP (@lem5715359 _119721 y x z) (@lem5715104 _119721 x y z)). Qed.
Lemma lem5715362 (b : Prop) (a : Prop) : (a \/ b) = (term442 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5715363 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term439 _119721 y x z) = (term443 _119721 x y z).
Proof. exact (@lem5715362 (term444 _119721 y x z) (y = z)). Qed.
Lemma lem5715365 (a : Prop) (b : Prop) : (term445 a b) = (term446 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5715366 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term447 _119721 y x z) = (term448 _119721 y x z).
Proof. exact (@lem5715365 (term435 _119721 x y) (term435 _119721 x z)). Qed.
Lemma lem5715368 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5715369 {_119721 : Type'} (x : _119721) (y : _119721) : (term449 _119721 x y) = (x = y).
Proof. exact (@lem5715368 (x = y)). Qed.
Lemma lem5715370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5715371 {_119721 : Type'} (x : _119721) (y : _119721) : (term450 _119721 x y) = (term451 _119721 x y).
Proof. exact (MK_COMB (@lem5715370) (@lem5715369 _119721 x y)). Qed.
Lemma lem5715373 (a : Prop) : (term18 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5715374 {_119721 : Type'} (x : _119721) (z : _119721) : (term449 _119721 x z) = (x = z).
Proof. exact (@lem5715373 (x = z)). Qed.
Lemma lem5715375 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term448 _119721 y x z) = (term452 _119721 y x z).
Proof. exact (MK_COMB (@lem5715371 _119721 x y) (@lem5715374 _119721 x z)). Qed.
Lemma lem5715376 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term447 _119721 y x z) = (term452 _119721 y x z).
Proof. exact (TRANS (@lem5715366 _119721 y x z) (@lem5715375 _119721 y x z)). Qed.
Lemma lem5715377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5715378 {_119721 : Type'} (y : _119721) (x : _119721) (z : _119721) : (term453 _119721 y x z) = (term454 _119721 y x z).
Proof. exact (MK_COMB (@lem5715377) (@lem5715376 _119721 y x z)). Qed.
Lemma lem5715379 {_119721 : Type'} (y : _119721) (z : _119721) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5715380 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term443 _119721 x y z) = (term455 _119721 x y z).
Proof. exact (MK_COMB (@lem5715378 _119721 y x z) (@lem5715379 _119721 y z)). Qed.
Lemma lem5715381 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : (term439 _119721 y x z) = (term455 _119721 x y z).
Proof. exact (TRANS (@lem5715363 _119721 x y z) (@lem5715380 _119721 x y z)). Qed.
Lemma lem5715383 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term498 _119721 b op a c.
Proof. exact (conj (@lem5715126 _119721 b c a op h1) (@lem5715270 _119721 b a c op h1)). Qed.
Lemma lem5715385 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (EQ_MP (@lem5715381 _119721 x y z) (@lem5715360 _119721 y x z)). Qed.
Lemma lem5715386 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (@lem5715385 _119721 x y z). Qed.
Lemma lem5715387 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : term499 _119721 b op a c.
Proof. exact (@lem5715386 _119721 (term376 _119721 b op c a) (term382 _119721 op b c a) (term376 _119721 b op a c)). Qed.
Lemma lem5715390 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op b c a) = (term376 _119721 b op a c).
Proof. exact (@lem5715387 _119721 b op a c (@lem5715383 _119721 b a c op h1)). Qed.
Lemma lem5715391 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op b c a) = (term376 _119721 b op a c).
Proof. exact (@lem5715390 _119721 b a c op h1). Qed.
Lemma lem5715392 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term500 _119721 b op a c.
Proof. exact (fun h0 : term501 _119721 b op a c => @lem5715391 _119721 b a c op h1). Qed.
Lemma lem5715394 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715395 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term500 _119721 b op a c) = ((term382 _119721 op b c a) = (term376 _119721 b op a c)).
Proof. exact (@lem5715394 ((term382 _119721 op b c a) = (term376 _119721 b op a c))). Qed.
Lemma lem5715396 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term382 _119721 op b c a) = (term376 _119721 b op a c).
Proof. exact (EQ_MP (@lem5715395 _119721 b op a c) (@lem5715392 _119721 b a c op h1)). Qed.
Lemma lem5715397 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term502 _119721 b op a c.
Proof. exact (conj (@lem5715117 _119721 a b c op h1) (@lem5715396 _119721 b a c op h1)). Qed.
Lemma lem5715399 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (EQ_MP (@lem5715381 _119721 x y z) (@lem5715360 _119721 y x z)). Qed.
Lemma lem5715400 {_119721 : Type'} (x : _119721) (y : _119721) (z : _119721) : term455 _119721 x y z.
Proof. exact (@lem5715399 _119721 x y z). Qed.
Lemma lem5715401 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : term503 _119721 b op a c.
Proof. exact (@lem5715400 _119721 (term382 _119721 op b c a) (term376 _119721 a op b c) (term376 _119721 b op a c)). Qed.
Lemma lem5715404 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 a op b c) = (term376 _119721 b op a c).
Proof. exact (@lem5715401 _119721 b op a c (@lem5715397 _119721 b a c op h1)). Qed.
Lemma lem5715405 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 a op b c) = (term376 _119721 b op a c).
Proof. exact (@lem5715404 _119721 b a c op h1). Qed.
Lemma lem5715406 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : term504 _119721 b op a c.
Proof. exact (fun h0 : term401 _119721 b op a c => @lem5715405 _119721 b a c op h1). Qed.
Lemma lem5715408 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715409 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term504 _119721 b op a c) = ((term376 _119721 a op b c) = (term376 _119721 b op a c)).
Proof. exact (@lem5715408 ((term376 _119721 a op b c) = (term376 _119721 b op a c))). Qed.
Lemma lem5715410 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term1 _119721 op) : (term376 _119721 a op b c) = (term376 _119721 b op a c).
Proof. exact (EQ_MP (@lem5715409 _119721 b op a c) (@lem5715406 _119721 b a c op h1)). Qed.
Lemma lem5715413 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5715415 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) : (term401 _119721 b op a c) = (term505 _119721 b op a c).
Proof. exact (@lem5715413 ((term376 _119721 a op b c) = (term376 _119721 b op a c))). Qed.
Lemma lem5715418 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term401 _119721 b op a c) : term505 _119721 b op a c.
Proof. exact (EQ_MP (@lem5715415 _119721 b op a c) (@lem5714518 _119721 b op a c h1)). Qed.
Lemma lem5715421 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : False.
Proof. exact (@lem5715418 _119721 b op a c h1 (@lem5715410 _119721 b a c op h2)). Qed.
Lemma lem5715422 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : term429.
Proof. exact (fun h0 : ~ False => @lem5715421 _119721 b a c op h1 h2). Qed.
Lemma lem5715424 (p : Prop) : (term427 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5715425 : term429 = False.
Proof. exact (@lem5715424 False). Qed.
Lemma lem5715426 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715425) (@lem5715422 _119721 b a c op h1 h2)). Qed.
Lemma lem5715427 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : (term401 _119721 b op a c) = False.
Proof. exact (prop_ext (fun h3 : term401 _119721 b op a c => @lem5715426 _119721 b a c op h1 h2) (fun h3 : False => @lem5714518 _119721 b op a c h1)). Qed.
Lemma lem5715428 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715427 _119721 b a c op h1 h2) (@lem5714518 _119721 b op a c h1)). Qed.
Lemma lem5715429 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : (term404 _119721 a op b c) = False.
Proof. exact (prop_ext (fun h3 : term404 _119721 a op b c => @lem5715064 _119721 a b c op h1 h2) (fun h3 : False => @lem5714510 _119721 a op b c h1)). Qed.
Lemma lem5715430 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715429 _119721 a b c op h1 h2) (@lem5714510 _119721 a op b c h1)). Qed.
Lemma lem5715431 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : (term407 _119721 op b a) = False.
Proof. exact (prop_ext (fun h3 : term407 _119721 op b a => @lem5714860 _119721 b a op h1 h2) (fun h3 : False => @lem5714502 _119721 op b a h1)). Qed.
Lemma lem5715432 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715431 _119721 b a op h1 h2) (@lem5714502 _119721 op b a h1)). Qed.
Lemma lem5715433 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : (term414 _119721 op a) = False.
Proof. exact (prop_ext (fun h3 : term414 _119721 op a => @lem5714791 _119721 a op h1 h2) (fun h3 : False => @lem5714494 _119721 op a h1)). Qed.
Lemma lem5715434 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715433 _119721 a op h1 h2) (@lem5714494 _119721 op a h1)). Qed.
Lemma lem5715435 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : (term417 _119721 op a) = False.
Proof. exact (prop_ext (fun h3 : term417 _119721 op a => @lem5714587 _119721 a op h1 h2) (fun h3 : False => @lem5714486 _119721 op a h1)). Qed.
Lemma lem5715436 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715435 _119721 a op h1 h2) (@lem5714486 _119721 op a h1)). Qed.
Lemma lem5715437 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : (term401 _119721 b op a c) = False.
Proof. exact (prop_ext (fun h3 : term401 _119721 b op a c => @lem5715428 _119721 b a c op h1 h2) (fun h3 : False => @lem5714388 _119721 b op a c h1)). Qed.
Lemma lem5715438 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715437 _119721 b a c op h1 h2) (@lem5714388 _119721 b op a c h1)). Qed.
Lemma lem5715439 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : (term404 _119721 a op b c) = False.
Proof. exact (prop_ext (fun h3 : term404 _119721 a op b c => @lem5715430 _119721 a b c op h1 h2) (fun h3 : False => @lem5714354 _119721 a op b c h1)). Qed.
Lemma lem5715440 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715439 _119721 a b c op h1 h2) (@lem5714354 _119721 a op b c h1)). Qed.
Lemma lem5715441 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : (term407 _119721 op b a) = False.
Proof. exact (prop_ext (fun h3 : term407 _119721 op b a => @lem5715432 _119721 b a op h1 h2) (fun h3 : False => @lem5714320 _119721 op b a h1)). Qed.
Lemma lem5715442 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715441 _119721 b a op h1 h2) (@lem5714320 _119721 op b a h1)). Qed.
Lemma lem5715443 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : (term414 _119721 op a) = False.
Proof. exact (prop_ext (fun h3 : term414 _119721 op a => @lem5715434 _119721 a op h1 h2) (fun h3 : False => @lem5714286 _119721 op a h1)). Qed.
Lemma lem5715444 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715443 _119721 a op h1 h2) (@lem5714286 _119721 op a h1)). Qed.
Lemma lem5715445 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : (term417 _119721 op a) = False.
Proof. exact (prop_ext (fun h3 : term417 _119721 op a => @lem5715436 _119721 a op h1 h2) (fun h3 : False => @lem5714252 _119721 op a h1)). Qed.
Lemma lem5715446 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715445 _119721 a op h1 h2) (@lem5714252 _119721 op a h1)). Qed.
Lemma lem5715447 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : (term401 _119721 b op a c) = False.
Proof. exact (prop_ext (fun h3 : term401 _119721 b op a c => @lem5715438 _119721 b a c op h1 h2) (fun h3 : False => @lem5714388 _119721 b op a c h1)). Qed.
Lemma lem5715448 {_119721 : Type'} (b : _119721) (a : _119721) (c : _119721) (op : type1400 _119721) (h1 : term401 _119721 b op a c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715447 _119721 b a c op h1 h2) (@lem5714388 _119721 b op a c h1)). Qed.
Lemma lem5715449 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : (term404 _119721 a op b c) = False.
Proof. exact (prop_ext (fun h3 : term404 _119721 a op b c => @lem5715440 _119721 a b c op h1 h2) (fun h3 : False => @lem5714354 _119721 a op b c h1)). Qed.
Lemma lem5715450 {_119721 : Type'} (a : _119721) (b : _119721) (c : _119721) (op : type1400 _119721) (h1 : term404 _119721 a op b c) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715449 _119721 a b c op h1 h2) (@lem5714354 _119721 a op b c h1)). Qed.
Lemma lem5715451 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : (term407 _119721 op b a) = False.
Proof. exact (prop_ext (fun h3 : term407 _119721 op b a => @lem5715442 _119721 b a op h1 h2) (fun h3 : False => @lem5714320 _119721 op b a h1)). Qed.
Lemma lem5715452 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term407 _119721 op b a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715451 _119721 b a op h1 h2) (@lem5714320 _119721 op b a h1)). Qed.
Lemma lem5715453 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : (term414 _119721 op a) = False.
Proof. exact (prop_ext (fun h3 : term414 _119721 op a => @lem5715444 _119721 a op h1 h2) (fun h3 : False => @lem5714286 _119721 op a h1)). Qed.
Lemma lem5715454 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term414 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715453 _119721 a op h1 h2) (@lem5714286 _119721 op a h1)). Qed.
Lemma lem5715455 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : (term417 _119721 op a) = False.
Proof. exact (prop_ext (fun h3 : term417 _119721 op a => @lem5715446 _119721 a op h1 h2) (fun h3 : False => @lem5714252 _119721 op a h1)). Qed.
Lemma lem5715456 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term417 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715455 _119721 a op h1 h2) (@lem5714252 _119721 op a h1)). Qed.
Lemma lem5715457 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term1 _119721 op) (h2 : term406 _119721 b op a c) : False.
Proof. exact (or_elim (@lem5714216 _119721 b op a c h2) (fun h0 : term404 _119721 a op b c => @lem5715450 _119721 a b c op h0 h1) (fun h0 : term401 _119721 b op a c => @lem5715448 _119721 b a c op h0 h1)). Qed.
Lemma lem5715458 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term1 _119721 op) (h2 : term409 _119721 b op a c) : False.
Proof. exact (or_elim (@lem5714214 _119721 b op a c h2) (fun h0 : term407 _119721 op b a => @lem5715452 _119721 b a op h0 h1) (fun h0 : term406 _119721 b op a c => @lem5715457 _119721 b op a c h1 h0)). Qed.
Lemma lem5715459 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term1 _119721 op) (h2 : term416 _119721 b op a c) : False.
Proof. exact (or_elim (@lem5714212 _119721 b op a c h2) (fun h0 : term414 _119721 op a => @lem5715454 _119721 a op h0 h1) (fun h0 : term409 _119721 b op a c => @lem5715458 _119721 b op a c h1 h0)). Qed.
Lemma lem5715460 {_119721 : Type'} (b : _119721) (op : type1400 _119721) (a : _119721) (c : _119721) (h1 : term1 _119721 op) (h2 : term357 _119721 b op a c) : False.
Proof. exact (or_elim (@lem5714206 _119721 b op a c h2) (fun h0 : term417 _119721 op a => @lem5715456 _119721 a op h0 h1) (fun h0 : term416 _119721 b op a c => @lem5715459 _119721 b op a c h1 h0)). Qed.
Lemma lem5715461 {_119721 : Type'} (b : _119721) (a : _119721) (op : type1400 _119721) (h1 : term360 _119721 b op a) (h2 : term1 _119721 op) : False.
Proof. exact (ex_elim (@lem5713807 _119721 b op a h1) (fun c : _119721 => fun h0 : term359 _119721 b op a c => @lem5715460 _119721 b op a c h2 h0)). Qed.
Lemma lem5715462 {_119721 : Type'} (a : _119721) (op : type1400 _119721) (h1 : term362 _119721 op a) (h2 : term1 _119721 op) : False.
Proof. exact (ex_elim (@lem5713806 _119721 op a h1) (fun b : _119721 => fun h0 : term361 _119721 op a b => @lem5715461 _119721 b a op h0 h2)). Qed.
Lemma lem5715463 {_119721 : Type'} (op : type1400 _119721) (h1 : term59 _119721 op) (h2 : term1 _119721 op) : False.
Proof. exact (ex_elim (@lem5713805 _119721 op h1) (fun a : _119721 => fun h0 : term363 _119721 op a => @lem5715462 _119721 a op h0 h2)). Qed.
Lemma lem5715464 {_119721 : Type'} (op : type1400 _119721) (h1 : term59 _119721 op) (h2 : term1 _119721 op) : (term1 _119721 op) = False.
Proof. exact (prop_ext (fun h3 : term1 _119721 op => @lem5715463 _119721 op h1 h2) (fun h3 : False => @lem5713306 _119721 op h2)). Qed.
Lemma lem5715465 {_119721 : Type'} (op : type1400 _119721) (h1 : term59 _119721 op) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715464 _119721 op h1 h2) (@lem5713306 _119721 op h2)). Qed.
Lemma lem5715466 {_119721 : Type'} (op : type1400 _119721) (h1 : term59 _119721 op) (h2 : term1 _119721 op) : (term59 _119721 op) = False.
Proof. exact (prop_ext (fun h3 : term59 _119721 op => @lem5715465 _119721 op h1 h2) (fun h3 : False => @lem5713250 _119721 op h1)). Qed.
Lemma lem5715467 {_119721 : Type'} (op : type1400 _119721) (h1 : term59 _119721 op) (h2 : term1 _119721 op) : False.
Proof. exact (EQ_MP (@lem5715466 _119721 op h1 h2) (@lem5713250 _119721 op h1)). Qed.
Lemma lem5715468 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term58 _119721 op.
Proof. exact (fun h0 : term59 _119721 op => @lem5715467 _119721 op h0 h1). Qed.
Lemma lem5715469 {_119721 : Type'} (op : type1400 _119721) (h1 : term1 _119721 op) : term4 _119721 op.
Proof. exact (EQ_MP (@lem5713249 _119721 op) (@lem5715468 _119721 op h1)). Qed.
Lemma lem5715470 {_119721 : Type'} (op : type1400 _119721) : term6 _119721 op.
Proof. exact (fun h0 : term1 _119721 op => @lem5715469 _119721 op h0). Qed.
Lemma lem5715475 {_119721 : Type'} : term10 _119721.
Proof. exact (fun op : type1400 _119721 => @lem5715470 _119721 op). Qed.
Lemma lem5715476 {_119721 : Type'} : term12 _119721.
Proof. exact (EQ_MP (@lem5713244 _119721) (@lem5715475 _119721)). Qed.
Lemma lem5715478 {_119721 : Type'} : term12 _119721.
Proof. exact (@lem5712951 _119721 (@lem5715476 _119721)). Qed.
Lemma lem5715479 {_119721 : Type'} (h1 : term13 _119721) : False.
Proof. exact (@lem5715478 _119721 (@lem5712935 _119721 h1)). Qed.
Lemma lem5715480 {_119721 : Type'} (h1 : term13 _119721) : (term13 _119721) = False.
Proof. exact (prop_ext (fun h2 : term13 _119721 => @lem5715479 _119721 h1) (fun h2 : False => @lem5712935 _119721 h1)). Qed.
Lemma lem5715481 {_119721 : Type'} (h1 : term13 _119721) : False.
Proof. exact (EQ_MP (@lem5715480 _119721 h1) (@lem5712935 _119721 h1)). Qed.
Lemma lem5715482 {_119721 : Type'} : term12 _119721.
Proof. exact (fun h0 : term13 _119721 => @lem5715481 _119721 h0). Qed.
Lemma lem5715483 {_119721 : Type'} : term10 _119721.
Proof. exact (EQ_MP (@lem5712934 _119721) (@lem5715482 _119721)). Qed.
Lemma lem5715484 {_119721 : Type'} : term9 _119721.
Proof. exact (EQ_MP (@lem5712930 _119721) (@lem5715483 _119721)). Qed.
