package cs.umass.edu.harshal

import actors.Futures._
import collection.mutable
import collection.mutable.{HashSet=>mSet}
import scala.Array


class Variable(n:String,c:Int){
  def name = n
  def cardinality = c
}

object Factor{

  def toPotential(value:Array[Double]) = for (i<-0 until value.length) value(i)=scala.math.exp(value(i))

  def calculateStrides(vars:Array[Variable]):Array[Int]={
    var acc = 1
    vars.map(v => {
      if (acc==1) {
        val ret = acc
        acc*=v.cardinality
        ret
      }
      else{
        val ret = acc
        acc*=v.cardinality
        ret
      }
    })
  }
}

class Factor(scpe:Set[Variable],strides:Array[Int],logSpace:Boolean=false,var value:Array[Double]=Array[Double]()){

  val stride = scope.zip(strides).toMap

  private lazy val size = scope.foldLeft(1)((acc,v)=>acc*v.cardinality)

  def :=(v:Array[Double]) = { assert(v.size==size);value=v }

  def scope = scpe
  //  if (!logSpace) for (i<-0 until value.length) value(i)=scala.math.exp(value(i))

  override def toString:String = {
    scope.map(_.name).mkString("")+" = "+"["+value.mkString(",")+"]"
  }

  def reduce(variable:Variable,assign:Int):Factor = {
    val scope = this.scope - variable
    val fScope = scope.toArray
    val strides = Factor.calculateStrides(fScope)
    val size = scope.foldLeft(1)((acc,v)=>acc*v.cardinality)
    val factor = new Factor(scope,strides,logSpace,Seq.fill(size)(0.0).toArray)
    val assignment = Seq.fill(scope.size)(0).toArray
    for (i <- 0 until size){
      val index = (0 until scope.size).foldLeft(0)((acc,l)=>
      {
        assignment(l) = (scala.math.floor(i/strides(l))%fScope(l).cardinality).toInt
        acc+assignment(l)*this.stride(fScope(l))
      })+assign*this.stride(variable)
      factor.value(i) = this(index)
    }
    factor
  }

  def *(f2:Factor):Factor={
    if (logSpace) this+f2
    else{
      if (f2==null) this
      else{
        var j = 0
        var k = 0
        val scope = this.scope.union(f2.scope)
        val fScope = scope.toArray
        val strides = Factor.calculateStrides(fScope)
        val size = scope.foldLeft(1)((acc,v)=>acc*v.cardinality)
        val factor = new Factor(scope,strides,logSpace,Seq.fill(size)(0.0).toArray)
        val assignment = Seq.fill(scope.size)(0).toArray
        for (i <- 0 until size){
          factor.value(i) = this.apply(j)*f2(k)
          var flag = true
          var l = 0
          while(flag && l<scope.size){
            assignment(l)+=1
            if (assignment(l)==fScope(l).cardinality){
              assignment(l) = 0
              j-=(fScope(l).cardinality-1)*this.stride.getOrElse(fScope(l),0)
              k-=(fScope(l).cardinality-1)*f2.stride.getOrElse(fScope(l),0)
              l+=1
            }else{
              j += this.stride.getOrElse(fScope(l),0)
              k += f2.stride.getOrElse(fScope(l),0)
              flag=false
            }
          }
        }
        factor
      }
    }
  }
  def +(f2:Factor):Factor={
    if (f2==null) this
    else{
      var j = 0
      var k = 0
      val scope = this.scope.union(f2.scope)
      val fScope = scope.toArray
      val strides = Factor.calculateStrides(fScope)
      val size = scope.foldLeft(1)((acc,v)=>acc*v.cardinality)
      val factor = new Factor(scope,strides,logSpace,Seq.fill(size)(0.0).toArray)
      val assignment = Seq.fill(scope.size)(0).toArray
      for (i <- 0 until size){
        factor.value(i) = this.apply(j)+f2(k)
        var flag = true
        var l = 0
        while(flag && l<scope.size){
          assignment(l)+=1
          if (assignment(l)==fScope(l).cardinality){
            assignment(l) = 0
            j-=(fScope(l).cardinality-1)*this.stride.getOrElse(fScope(l),0)
            k-=(fScope(l).cardinality-1)*f2.stride.getOrElse(fScope(l),0)
            l+=1
          }else{
            j += this.stride.getOrElse(fScope(l),0)
            k += f2.stride.getOrElse(fScope(l),0)
            flag=false
          }
        }
      }
      factor
    }
  }

  def marginalize(variable:Variable):Factor={
    if (logSpace) marginalizeInLog(variable)
    else{
      val scope = this.scope - variable
      val fScope = scope.toArray
      val strides = Factor.calculateStrides(fScope)
      val size = scope.foldLeft(1)((acc,v)=>acc*v.cardinality)
      val factor = new Factor(scope,strides,logSpace,Seq.fill(size)(0.0).toArray)
      val assignment = Seq.fill(scope.size)(0).toArray
      for (i <- 0 until size){
        factor.value(i) = (0 until variable.cardinality).foldLeft(0.0)((acc,j)=>{
          val index = (0 until scope.size).foldLeft(0)((acc,l)=>
          {
            assignment(l) = (scala.math.floor(i/strides(l))%fScope(l).cardinality).toInt
            acc+assignment(l)*this.stride(fScope(l))
          })+j*this.stride(variable)
          acc+this.value(index)
        })
      }
      factor
    }
  }

  def marginalizeInLog(variable:Variable):Factor={
    val scope = this.scope - variable
    val fScope = scope.toArray
    val strides = Factor.calculateStrides(fScope)
    val size = scope.foldLeft(1)((acc,v)=>acc*v.cardinality)
    val factor = new Factor(scope,strides,logSpace,Seq.fill(size)(0.0).toArray)
    val assignment = Seq.fill(scope.size)(0).toArray
    for (i <- 0 until size){
      val temp = (0 until variable.cardinality).map(j=>{
        val index = (0 until scope.size).foldLeft(0)((acc,l)=>
        {
          assignment(l) = (scala.math.floor(i/strides(l))%fScope(l).cardinality).toInt
          acc+assignment(l)*this.stride(fScope(l))
        })+j*this.stride(variable)
        this.value(index)
      })
      factor.value(i) = logsumexp(temp)
    }
    factor
  }

  def logsumexp(vals:Seq[Double])= {
    val max = vals.max
    val logsum = math.log(vals.foldLeft(0.0)((acc,d)=>acc+math.exp(d-max)))
    max + logsum
  }

  def partitionFn = {
    val tempf = this.scope.tail.foldLeft(null.asInstanceOf[Factor])((_,v)=>this.marginalize(v))
    if (logSpace) logsumexp(tempf.value)
    else tempf.value.foldLeft(0.0)((acc,d)=>acc+d)
  }

  def apply(index:Int) = value(index)
}

class CliqueTree(cs:Array[Clique],var status:Int = 0){
  def cliques = cs
  lazy val reverse = cliques.reverse
  def done:Boolean = status==cliques.size
}

case class Clique(factors:Set[Factor],neighbors:mSet[Clique]= mSet[Clique]()){
  var psi = factors.foldLeft(null.asInstanceOf[Factor])((acc,f)=> f*acc)
  val incoming:mSet[Factor] = mSet[Factor]()
  val downstream = mSet[Clique]()
  var outgoing:mSet[Factor] = mSet[Factor]()
  lazy val scope = factors.foldLeft(Set[Variable]())((acc,f)=>acc.union(f.scope))
  lazy val receiver = neighbors.diff(downstream)
  //  def ready:Boolean = if (neighbors.size==1) true
  //  else if (downstream.size==neighbors.size-1) true
  //  else false
  //  def done:Boolean = outgoing!=null

  def getNeighbors = neighbors

  lazy val beta = {
    assert(outgoing!=null,"Clique not ready yet")
    val temp = incoming.foldLeft(psi)((psi,f)=>psi*f)
    outgoing.foldLeft(temp)((psi,f)=>psi*f)
  }
}

class Inference(cTree:CliqueTree){
  def infer {
    val tasks = Seq(
      future(
        for (i<-0 until cTree.cliques.length-1)
          cTree.cliques(i+1).incoming+=BUMessage(cTree.cliques(i),cTree.cliques(i+1),true)
      ),
      future(
        for (i<-0 until cTree.cliques.length-1)
          cTree.reverse(i+1).outgoing+=BUMessage(cTree.reverse(i),cTree.reverse(i+1),false)
      )
    )
    awaitAll(3600000,tasks: _*)
    //    while(!cTree.done){
    //      cTree.cliques.find(c=> !c.done && c.ready) match {
    //      case Some(clique) => {
    //        assert(clique.receiver.size==1,"Multiple receivers")
    //        clique.receiver.head
    //        BUMessage(clique,clique.receiver.head)
    //        clique.receiver.head.incoming += clique.outgoing
    //        clique.receiver.head.downstream += clique
    //      }
    //      case None =>
    //    }
    //  }
  }
  def BUMessage(sender:Clique,receiver:Clique,l2r:Boolean)={
    val temp = if(l2r) sender.incoming.foldLeft(sender.psi)((acc,f)=> f*acc)
    else sender.outgoing.foldLeft(sender.psi)((acc,f)=> f*acc)
    //    sender.outgoing = sender.scope.diff(receiver.scope).foldLeft(sender.psi)((psi,v)=>psi.marginalize(v))
    cTree.status+=1
    sender.scope.diff(receiver.scope).foldLeft(temp)((psi,v)=>psi.marginalize(v))
  }
}

final class Feature(name:String,cardinality:Int) extends Variable(name,cardinality)
final class Label(name:String,cardinality:Int) extends Variable(name,cardinality)

case class Token(values:Array[Int])

class CRFModel(length:Int){
  val features = Array(new Feature("bias",1),
    new Feature("Initial Capital",2),
    new Feature("All Capitals",2),
    new Feature("Prefix ID",201),
    new Feature("Siffix ID",201))

  val label = new Label("POS Tag",10)

//  val labelFactors = (1 to length).map( _ => new Factor(Set(label),Factor.calculateStrides(Array(label)),true) ).toArray

  val featuresFactors = new Factor((features+label).toSet,Factor.calculateStrides((features+label)),true)

  val pariwiseFactors = (1 until length).map(_ => new Factor(Set(label,label),Factor.calculateStrides(Array(label,label)),true) ).toArray

  def getCliques(labelFactors:Array[Factor]) = {
    labelFactors.take(length-2).zip(pariwiseFactors.take(length-2)).map( f => new Clique(Set(f._1,f._2)) ) ++
      new Clique( (labelFactors.takeRight(2) + pariwiseFactors.last).toSet )
  }

  def setNeighbors(cliques:Array[Clique]) = {
    for (i <- 0 until cliques.length){
      if (i==0 ) { cliques(i).neighbors ++ cliques(i+1) }
      else if (i==cliques.length-1) { cliques(i).neighbors ++ cliques(i-1) }
      else { cliques(i).neighbors++ Seq(cliques(i-1),cliques(i+1)) }
    }
  }

  def getCTree(instance:Array[Token])={
    val reduced = instance.map( token => {
      features.zipWithIndex.foldLeft(featuresFactors)((fact,feat)=> fact.reduce(feat._1,token(feat._2)) )
    })
    val cliques = getCliques(reduced)
    setNeighbors(cliques)
    new CliqueTree(cliques)
  }

  def likelihood(weights:Array[Double]):Double={
     null

  }
}



object Runner extends App{
//  val y1 = Variable("y1",2)
//  val y2 = Variable("y2",2)
//  val y3 = Variable("y3",2)
//  val y4 = Variable("y4",2)
//  val phi1 = new Factor(Array(0.0,1.0),Set(y1),Factor.calculateStrides(Array(y1)),true)
//  val phi2 = new Factor(Array(1.0,0.0),Set(y2),Factor.calculateStrides(Array(y2)),true)
//  val phi3 = new Factor(Array(0.0,1.0),Set(y3),Factor.calculateStrides(Array(y3)),true)
//  val phi4 = new Factor(Array(0.0,1.0),Set(y4),Factor.calculateStrides(Array(y4)),true)
//  val phi12 = new Factor(Array(2.0,1.0,1.0,2.0),Set(y1,y2),Factor.calculateStrides(Array(y1,y2)),true)
//  val phi23 = new Factor(Array(2.0,1.0,1.0,2.0),Set(y2,y3),Factor.calculateStrides(Array(y2,y3)),true)
//  val phi34 = new Factor(Array(2.0,1.0,1.0,2.0),Set(y3,y4),Factor.calculateStrides(Array(y3,y4)),true)
//  val c1 = new Clique(Set(phi1,phi12))
//  val c2 = new Clique(Set(phi2,phi23))
//  val c3 = new Clique(Set(phi3,phi4,phi34))
//  c1.getNeighbors+=c2
//  c2.getNeighbors++=Seq(c1,c3)
//  c3.getNeighbors+=c2
//  val cTree = CliqueTree(Array(c1,c2,c3))
//  new Inference(cTree).infer
//  println(c1.beta)
//  println(c2.beta)
//  println(c3.beta)
//  c3.beta.value.foreach(v=>println(math.exp(v-c3.beta.partitionFn)))
//  val x1 = Variable("x1",2)
//  val x = new Factor(Array(1.0,0.0,0.0,1.0),Set(x1,y1),Factor.calculateStrides(Array(x1,y1)),true)
//  println(x.reduce(x1,1))

}