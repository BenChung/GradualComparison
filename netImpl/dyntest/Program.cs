using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace dyntest
{
    namespace Kafka
    {
        class A
        {
            public A()
            {

            }
            public A m(A x)
            {
                return this;
            }

        }
        class I
        {
            public I()
            {

            }
            public I m(C x)
            {
                return this;
            }

        }
        class T
        {
            public T()
            {

            }
            public T s(I x)
            {
                return this;
            }

            public dynamic t(dynamic x)
            {
                return (dynamic)this.s((I)x);
            }

        }
        class C
        {
            public C()
            {

            }
            public C n(C x)
            {
                return this;
            }

        }
        class Program
        {
            public static void Main(string[] args)
            {
                (dynamic)new T().t((dynamic)new A());
            }
        }
    }
}
