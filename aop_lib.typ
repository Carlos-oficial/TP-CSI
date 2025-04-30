
#let split(f, g) = $ angle.l #f, #g angle.r $
#let splitn(f) = $ angle.l #f angle.r $
#let p1 = $pi_1$
#let p2 = $pi_2$
#let prod(f, g) = $ #f times.circle #g $
#let either(f, g) = $ [ #f, #g ] $
#let coprod(f, g) = $ #f plus.circle #g $
#let i1 = $i_1$
#let i2 = $i_2$


#let cata(f) = $ \u{2987} #f \u{2988} $
#let ana(f) = $ \u{3016} #f \u{3017} $
#let hylo(f,g) = $ [| #f,#g |] $
#let para(f) = $ \u{2989} #f \u{298A} $
#let inT = $ "in" $
#let oplus = $ plus.circle $
#let otimes = $ times.circle $

#let bigDot = math.circle.filled.small
#let anaf(funcor,f) = $ \u{3016} #f \u{3017}_functor $
#let cataf(functor,f) = $ \u{0265B} #f \u{2988}_functor $
#let n0 = $NN_0$
#let const(f) = $ underline(#f) $
#let bigO(n,c) = $ cal(O)^(#n)_#c $
#let list(a) = $ #a^(*) $ 

#let dist = $ cal(D) $
#let distT = $ cal(D) cal(T) $

#let inv(f) = $ #f^circle.small  $
#let uncurry(a) = $ accent(#a,hat) $


#let justeq(just) = $ \ equiv space { #just } \  $
#let justimp(just) = $ \ => space { #just } \  $
#let just(sym, just) = $ \ #sym space { #just } \ $
#let justimp(just) = $ \ <== space { #just } \ $ 

#let subs(new, old) = $attach(slash,tl:new,br:old) $

#let rcb(q,v,r,t) = $ angle.l #q #v : #r : #t angle.r $ 
#let sse(p,q) = $ #p space subset.eq space #q $ 
#let infix(a,o,b) = $ #a space #o space #b $ 
#let crflx(p) = $#p?$
#let rdiv(r,s) = $ #r backslash #s $ 

#let bottom = $ tack.t $
#let top = $ tack.b $
#let pw(r) = $ accent(#r,.)$ 
