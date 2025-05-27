
class A{
    int a;
    String s;
    A(int x,String z)
    {
        a = 2*x;
        s = z;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true; // Same reference
        if (obj == null || getClass() != obj.getClass()) return false; // Null or different class

        // Compare fields of class A
        A other = (A) obj;
        return a == other.a && s.equals(other.s);
    }
}

public class Benchmark3 extends A {
    int a;
    int b;
    Benchmark3(int x, int y,String z)
    {
        super(2*x+y,z);
        a = 3*x;
        b = 4*y;

    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        // Call parent class equals
        if (!super.equals(obj)) return false;

        // Check child class fields
        Benchmark3 other = (Benchmark3) obj;
        return this.a == other.a && this.b == other.b;
    }


    public static void main(String[] args) {
        long startTime = System.currentTimeMillis();

        Benchmark3[] benchmarkArray = new Benchmark3[1000000];
        
        for(int i=0;i<1000000;++i)
        {
        	int x = i*100;
        	int y = i+1000;
            benchmarkArray[i] = new Benchmark3(2, 4,"Hello");
        }
        
        for(int i=0;i<100000;++i)
        {
            for(int j=i+1;j<1000000;++j)
            {
                if(benchmarkArray[i].equals(benchmarkArray[j]))
                {
                    // System.out.println("Objects are equal ");
                }
                else
                {
                    // System.out.println("Objects are not equal ");
                }
            }
        }
        
        
        
        long endTime = System.currentTimeMillis();
        
        System.out.println("Time taken: " + (endTime - startTime) + " ms");
    }
}
