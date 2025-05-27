import java.io.*;
import java.util.Objects;
import java.util.HashMap;


class Example2 {
    int a;
    int b;
    int c;
    public static HashMap objectPool = new HashMap();

    // Example2(int a, int b) {
    //     super();
    //     this.a = a;
    //     this.b = b;
    //     this.c = a + b;
    // }

    Example2(int a,int b,int c)
    {
        super();
        this.a = a;
        this.b = b;
        this.c = c;
    }

    public static int generateCustomHash(int a, int b,int c) {
        return Objects.hash(a, b, c);
    }

    public static Example2 createObject(int a,int b,int c)
    {
        int hashValue = generateCustomHash(a,b,c);
        Example2 ansObject;
        if (objectPool.containsKey(hashValue)) {
            ansObject = (Example2) objectPool.get(hashValue);
        } else {
            ansObject = new Example2(a, b, c);
            objectPool.put(hashValue, ansObject);
        }
        return ansObject;

    }

    public static Example2 dummyConstructor1(int a,int b)
    {
        int this_a,this_b,this_c;
        this_a = a;
        this_b = b;
        this_c = a+b;
        return createObject(this_a,this_b,this_c);
    }
 
    public static void main(String[] args) {
        Example2 a = dummyConstructor1(5,10);
        Example2 b = dummyConstructor1(5,10);

        if(a.equals(b))
        {
            System.out.println("Objects are equal");
        }
        else
        {
            System.out.println("Objects are not equal");
        }

    }
}
