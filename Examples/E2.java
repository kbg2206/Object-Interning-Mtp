import java.io.*;
import java.util.Objects;
import java.util.HashMap;

class E2 {

    int a;
    int b;
    int c;

    E2(int a,int b)
    {
//        super();
        this.a = a;
        this.b = b;
//        System.out.println("hello");
        this.c = a+b;
    }


    public static void main(String[] args) {
        E2 a = new E2(5,10);
        E2 b = new E2(5,10);

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
