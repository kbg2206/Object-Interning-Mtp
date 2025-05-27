// package Fifth;
import java.util.HashMap;
import java.util.Objects;


class Dummy{

}


class B{
    int a;
    int b;
    public static HashMap objectPool = new HashMap();

    B(int x)
    {
        super();
        a = x;
        b = 2 * x;
    }

    B(int x, int y)
    {
        super();
        a = x;
        b = y;
    }

    B(Dummy dummy1,int this_a,int this_b)
    {
        super();
        a = this_a;
        b = this_b;
    }

    B(Dummy dummy1,Dummy dummy2,int this_a,int this_b)
    {
        super();
        a = this_a;
        b = this_b;
    }

    public static int generateCustomHash(int this_a,int this_b)
    {
        return Objects.hash(this_a,this_b);
    }

    public static int HashFunctionB(B obj)
    {
        return Objects.hash(obj.a,obj.b);
    }

    @Override
    public int hashCode() {
        return Objects.hash(a, b);
    }

    public static B createObjectB1(int this_a, int this_b)
    {
        int hashValue = generateCustomHash(this_a, this_b);
        if (objectPool.containsKey(hashValue)) {
            return (B) objectPool.get(hashValue);
        }
        else{
            B ansobj = new B(null,this_a,this_b);
            objectPool.put(hashValue, ansobj);
            return ansobj;
        }
    }

    public static B createObjectB2(int this_a, int this_b)
    {
        int hashValue = generateCustomHash(this_a, this_b);
        if (objectPool.containsKey(hashValue)) {
            return (B) objectPool.get(hashValue);
        }
        else{
            B ansobj = new B(null,null,this_a,this_b);
            objectPool.put(hashValue, ansobj);
            return ansobj;
        }
    }

    public static B dummyConstructorB1(int x,boolean flag)
    {
        if(flag)
        {
            int this_a,this_b;
            this_a = x;
            this_b = 2 * x;
            B ans = createObjectB1(this_a,this_b);
            return ans;
        }
        else
        {
            return new B(x);
        }
        
    }

    public static B dummyConstructorB2(int x, int y,boolean flag)
    {
        if(flag)
        {
            int this_a,this_b;
            this_a = x;
            this_b = y;
            B ans = createObjectB2(this_a,this_b);
            return ans;
        }
        else
        {
            return new B(x,y);
        }
        
    }
}

public class A extends B{
    int c,d;
    public static HashMap objectPool = new HashMap();

    A(int x,int y)
    {
        super(x);
        c = x;
        d = y;
    }

    A(int x,int y,int z)
    {
        super(z,2*z);
        c = x;
        d = y;
    }

    A(Dummy dummy1,int this_c,int this_d,int exp1)
    {
        super(exp1);
        c = this_c;
        d = this_d;
    }

    A(Dummy dummy1,Dummy dummy2,int this_c,int this_d,int exp1,int exp2)
    {
        super(exp1,exp2);
        c = this_c;
        d = this_d;
    }

    public static int generateCustomHash(int this_c, int this_d, int hashv)
    {
        return Objects.hash(this_c,this_d,hashv);
    }


    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(),c, d);
    }

    public static A createObjectA1(int this_c,int this_d,int hashV,int exp1)
    {
        int hashValue = generateCustomHash(this_c,this_d,hashV);
        if (objectPool.containsKey(hashValue)) {
            return (A) objectPool.get(hashValue);
        }
        else{
            A ansobj = new A(null,this_c,this_d,exp1);
            objectPool.put(hashValue, ansobj);
            return ansobj;
        }
    }

    public static A dummyConstructorA1(int x,int y,boolean flag)
    {
        if(flag)
        {
            int this_c,this_d;
            B obj = B.dummyConstructorB1(x,false);
            int hashV = obj.hashCode();
            this_c = x;
            this_d = y;
            A ans = createObjectA1(this_c,this_d,hashV,x);
            return ans;
        }
        else
        {
            return new A(x,y);
        }
        

    }

    public static A createObjectA2(int this_c,int this_d,int hashV,int exp1,int exp2)
    {
        int hashValue = generateCustomHash(this_c,this_d,hashV);
        if (objectPool.containsKey(hashValue)) {
            return (A) objectPool.get(hashValue);
        }
        else{
            A ansobj = new A(null,null,this_c,this_d,exp1,exp2);
            objectPool.put(hashValue, ansobj);
            return ansobj;
        }
    }

    public static A dummyConstructorA2(int x, int y, int z,boolean flag)
    {
        if(flag)
        {
            B obj = B.dummyConstructorB2(z,2*z,false);
            int hashV = B.HashFunctionB(obj);
            int this_c = x;
            int this_d = y;
            A ans = createObjectA2(this_c,this_d,hashV,z,2*z);
            return ans;
        }
        else
        {
            return new A(x,y,z);
        }
        
    }

    public static void main(String[] args) {
        A o1 = dummyConstructorA1(3,4,true);
        A o2 = dummyConstructorA2(3,4,3,true);
        if(o1.equals(o2))
        {
            System.out.println("Objects are equal");
        }
        else
        {
            System.out.println("Objects are not equal");
        }

        System.out.println(o1.hashCode());
        System.out.println(o2.hashCode());
    }
}
