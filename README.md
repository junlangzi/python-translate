# Phần mềm dịch nội dung file Python sang ngôn ngữ khác!

**Phầm mềm có những tính năng sau:**

* Quét và quản lý các comment trong file python ( xoá hoặc sửa )
* Quét các phần trong file python để dịch:
* Chạy thử file kiểm tra lỗi trước khi lưu

**Quét để dịch file Python có các tuỳ chọn sau:**

* Hệ thống tự quét thông minh, tự nhận diện ( tự nhận diện ngôn ngữ và nhận diện phần cần dịch )
* Quét nhờ sự trợ giúp của Gemini
* Có chế độ quét an toàn AST+content để hạn chế quét nhầm gây lỗi
* Tuỳ chọn số lượng từ dịch trong 1 lần request, giới hạn số request trên phút.
* Khi quét lỗi sẽ quét lại, nếu tiếp tục lỗi sẽ phân nhỏ từng đoạn để quét, trường hợp lỗi liên tục sẽ bỏ qua vị trí đó để tiến hành quét tiếp

**Dịch file bằng API của Gemini**

Code cài đặt các gói cần thiết bổ sung để chạy chương trình

```
pip install ttkbootstrap google-generativeai langdetect
```


<br>
Ảnh demo:

![image](https://raw.githubusercontent.com/junlangzi/python-translate/refs/heads/main/demo.png)

<br>
