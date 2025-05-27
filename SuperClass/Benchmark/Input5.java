class A{
    int a;
    A(int x)
    {
        a = x;
    }
}

public class Input5 extends A {
    int b;
    A o1;
    Input5(int x)
    {
        super(x);
        b = 2*x;
        o1 = new A(x+1);
    }
    public static void main(String[] args) {
        Input5 o1 = new Input5(1);
        Input5 o2 = new Input5(1);
        if(o1.equals(o2))
        {
            System.out.println("Objects are equal");
        }
        else
        {
            System.out.println("Objects are not equal");
        }
    }
}
